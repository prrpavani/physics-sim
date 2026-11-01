// Draws the universe. Every position comes from a frame the Lean model produced; the scene only blends
// between two frames for smooth motion. No physics here.

import { Canvas, useFrame, useThree } from "@react-three/fiber";
import { Grid, Html, OrbitControls, Stars } from "@react-three/drei";
import { Bloom, EffectComposer, Vignette } from "@react-three/postprocessing";
import { useEffect, useMemo, useRef } from "react";
import * as THREE from "three";
import type { Body, Bounds, Field, Portal, Region, World } from "../../../../shared/types/paradox";
import { num, vecNums } from "../lib/num";
import { clock, TICKS_PER_SECOND, useStore } from "../store";

type V3 = [number, number, number];
const TRAIL_LENGTH = 70;

const boundsCentre = (b: Bounds): V3 => [
  (num(b.minX) + num(b.maxX)) / 2, (num(b.minY) + num(b.maxY)) / 2, (num(b.minZ) + num(b.maxZ)) / 2,
];
const boundsSize = (b: Bounds): V3 => [
  Math.max(num(b.maxX) - num(b.minX), 0.001), Math.max(num(b.maxY) - num(b.minY), 0.001), Math.max(num(b.maxZ) - num(b.minZ), 0.001),
];

/** The position and velocity to draw. Blended between frames while playing. */
function drawnBody(id: number): { position: V3; velocity: V3; body: Body } | null {
  const now = clock.current?.bodies.find(b => b.id === id);
  if (!now) return null;
  const prev = clock.previous?.bodies.find(b => b.id === id);
  const end = now.renderPosition ?? vecNums(now.position);
  const velocity = (now.renderVelocity ?? vecNums(now.velocity)) as V3;
  if (!prev) return { position: end as V3, velocity, body: now };
  const start = prev.renderPosition ?? vecNums(prev.position);
  // A large jump is a portal or wrap, not motion. Do not draw the body sliding across the world.
  const jump = Math.hypot(end[0] - start[0], end[1] - start[1], end[2] - start[2]);
  const a = jump > 4 ? 1 : clock.alpha;
  return {
    position: [start[0] + (end[0] - start[0]) * a, start[1] + (end[1] - start[1]) * a, start[2] + (end[2] - start[2]) * a],
    velocity, body: now,
  };
}

function bodyColor(b: Body): THREE.Color {
  const q = num(b.charge);
  if (q > 0) return new THREE.Color("#ff7a59");
  if (q < 0) return new THREE.Color("#5aa9ff");
  return new THREE.Color("#c8fff0");
}

function BodyMesh({ id, limit }: { id: number; limit: number }) {
  const group = useRef<THREE.Group>(null);
  const mat = useRef<THREE.MeshStandardMaterial>(null);
  const line = useRef<THREE.BufferGeometry>(null);
  const arrow = useRef<THREE.ArrowHelper>(null);
  const halo = useRef<THREE.Mesh>(null);
  const trail = useMemo(() => new Float32Array(TRAIL_LENGTH * 3), []);
  const colors = useMemo(() => new Float32Array(TRAIL_LENGTH * 3), []);
  const filled = useRef(0);
  const select = useStore(s => s.select);
  const isSelected = useStore(s => s.selected === id);
  const initial = clock.current?.bodies.find(b => b.id === id);
  const shape = initial?.shape;
  const size = initial ? num(shape!.type === "sphere" ? shape!.radius : shape!.halfWidth) : 0.5;
  const base = useMemo(() => (initial ? bodyColor(initial) : new THREE.Color("white")), [initial?.charge]);
  const hot = useMemo(() => new THREE.Color("#ff2d55"), []);
  const showTrail = useStore(s => s.showTrails);
  const showVectors = useStore(s => s.showVectors);
  const dir = useMemo(() => new THREE.Vector3(), []);

  useFrame(() => {
    const d = drawnBody(id);
    if (!d || !group.current) return;
    const [x, y, z] = d.position;
    group.current.position.set(x, y, z);
    const speed = Math.max(Math.abs(d.velocity[0]), Math.abs(d.velocity[1]), Math.abs(d.velocity[2]));
    const over = limit > 0 ? speed > limit + 1e-6 : speed > 0;
    const ratio = Math.min(speed / Math.max(limit, 1), 1);

    if (mat.current) {
      mat.current.color.copy(over ? hot : base);
      mat.current.emissive.copy(over ? hot : base);
      mat.current.emissiveIntensity = over ? 3 : 0.25 + ratio * 1.5;
    }
    if (halo.current) {
      const pulse = isSelected ? 1.55 + Math.sin(performance.now() / 200) * 0.08 : 0;
      halo.current.visible = isSelected;
      halo.current.scale.setScalar(pulse);
    }

    // The trail is a ring of past drawn positions, newest first.
    trail.copyWithin(3, 0, (TRAIL_LENGTH - 1) * 3);
    trail[0] = x; trail[1] = y; trail[2] = z;
    filled.current = Math.min(filled.current + 1, TRAIL_LENGTH);
    for (let i = 0; i < TRAIL_LENGTH; i++) {
      const fade = Math.pow(1 - i / TRAIL_LENGTH, 2);
      const c = over ? hot : base;
      colors[i * 3] = c.r * fade; colors[i * 3 + 1] = c.g * fade; colors[i * 3 + 2] = c.b * fade;
    }
    if (line.current) {
      line.current.attributes.position.needsUpdate = true;
      line.current.attributes.color.needsUpdate = true;
      line.current.setDrawRange(0, filled.current);
    }
    if (arrow.current) {
      const len = Math.hypot(...d.velocity);
      arrow.current.visible = showVectors && len > 0.01;
      if (len > 0.01) {
        dir.set(d.velocity[0] / len, d.velocity[1] / len, d.velocity[2] / len);
        arrow.current.setDirection(dir);
        arrow.current.setLength(Math.min(0.5 + len * 0.25, 6), 0.3, 0.18);
      }
    }
  });

  if (!shape) return null;
  return (
    <>
      <group ref={group}>
        <mesh onClick={e => { e.stopPropagation(); select(isSelected ? null : id); }}
          onPointerOver={() => { document.body.style.cursor = "pointer"; }}
          onPointerOut={() => { document.body.style.cursor = "auto"; }}>
          {shape.type === "sphere"
            ? <sphereGeometry args={[size, 32, 20]} />
            : <boxGeometry args={[size * 2, size * 2, size * 2]} />}
          <meshStandardMaterial ref={mat} metalness={0.2} roughness={0.25} toneMapped={false} />
        </mesh>
        <mesh ref={halo} visible={false}>
          <sphereGeometry args={[size, 24, 16]} />
          <meshBasicMaterial color="#ffffff" wireframe transparent opacity={0.45} />
        </mesh>
        <primitive ref={arrow} object={useMemo(() => new THREE.ArrowHelper(new THREE.Vector3(1, 0, 0), new THREE.Vector3(), 1, 0xffd166), [])} visible={false} />
      </group>
      {showTrail && (
        <line>
          <bufferGeometry ref={line}>
            <bufferAttribute attach="attributes-position" args={[trail, 3]} />
            <bufferAttribute attach="attributes-color" args={[colors, 3]} />
          </bufferGeometry>
          <lineBasicMaterial vertexColors transparent opacity={0.9} toneMapped={false} />
        </line>
      )}
    </>
  );
}

/** The world's walls. Calm when guarantees are protected, alarmed when one has broken. */
function Walls({ bounds, torus }: { bounds: Bounds; torus: boolean }) {
  const mode = useStore(s => s.mode);
  const broken = useStore(s => s.guarantees && Object.values(s.guarantees).includes("violated"));
  const replaying = useStore(s => !!s.replay);
  const material = useRef<THREE.LineBasicMaterial>(null);
  const size = boundsSize(bounds);
  const centre = boundsCentre(bounds);
  const edges = useMemo(() => new THREE.EdgesGeometry(new THREE.BoxGeometry(...size)), [size[0], size[1], size[2]]);
  const color = broken || replaying ? "#ff2d55" : torus ? "#c792ff" : mode === "protected" ? "#35f0c4" : "#ffb74d";

  useFrame(({ clock: c }) => {
    if (material.current) {
      const pulse = broken || replaying ? 1.8 + Math.sin(c.elapsedTime * 7) * 1.2 : 1.2 + Math.sin(c.elapsedTime * 1.5) * 0.2;
      material.current.color.set(color).multiplyScalar(pulse);
    }
  });

  return (
    <group position={centre}>
      <lineSegments geometry={edges}>
        <lineBasicMaterial ref={material} toneMapped={false} />
      </lineSegments>
      <mesh>
        <boxGeometry args={size} />
        <meshBasicMaterial color={color} transparent opacity={0.018} side={THREE.BackSide} depthWrite={false} />
      </mesh>
    </group>
  );
}

function RegionBox({ region }: { region: Region }) {
  const size = boundsSize(region.box);
  const centre = boundsCentre(region.box);
  const scale = num(region.timeScale);
  return (
    <group position={centre}>
      <mesh>
        <boxGeometry args={size} />
        <meshBasicMaterial color={region.color || "#88aaff"} transparent opacity={0.09} depthWrite={false} />
      </mesh>
      <lineSegments>
        <edgesGeometry args={[new THREE.BoxGeometry(...size)]} />
        <lineBasicMaterial color={region.color || "#88aaff"} transparent opacity={0.6} />
      </lineSegments>
      <Html center position={[0, size[1] / 2 + 0.4, 0]} className="scene-label" distanceFactor={22} zIndexRange={[5, 0]}>
        {region.name}{scale !== 1 ? ` · time ×${scale.toFixed(2)}` : ""}
      </Html>
    </group>
  );
}

function FieldBox({ field }: { field: Field }) {
  const size = boundsSize(field.region);
  const centre = boundsCentre(field.region);
  const a = vecNums(field.acceleration);
  const len = Math.hypot(...a);
  const dir = useMemo(() => new THREE.Vector3(...a).normalize(), [a[0], a[1], a[2]]);
  return (
    <group position={centre}>
      <lineSegments>
        <edgesGeometry args={[new THREE.BoxGeometry(...size)]} />
        <lineDashedMaterial color="#ffd166" transparent opacity={0.45} />
      </lineSegments>
      {len > 0 && <primitive object={new THREE.ArrowHelper(dir, new THREE.Vector3(), Math.min(1 + len * 0.1, size[1] / 2), 0xffd166, 0.6, 0.35)} />}
    </group>
  );
}

function PortalRing({ portal }: { portal: Portal }) {
  const ring = useRef<THREE.Mesh>(null);
  const size = boundsSize(portal.entrance);
  const centre = boundsCentre(portal.entrance);
  const radius = Math.max(Math.min(Math.max(size[0], size[2]) / 2, 5), 0.8);
  const exit = portal.exit ? vecNums(portal.exit) : null;
  useFrame((_, dt) => { if (ring.current) ring.current.rotation.z += dt * 0.9; });
  return (
    <>
      <mesh position={centre} ref={ring} rotation={[Math.PI / 2, 0, 0]}>
        <torusGeometry args={[radius, 0.09, 12, 56]} />
        <meshStandardMaterial color="#b388ff" emissive="#b388ff" emissiveIntensity={2.2} toneMapped={false} />
      </mesh>
      {exit ? (
        <mesh position={exit} rotation={[Math.PI / 2, 0, 0]}>
          <torusGeometry args={[Math.min(radius, 1.2), 0.06, 12, 40]} />
          <meshStandardMaterial color="#00e5ff" emissive="#00e5ff" emissiveIntensity={2} toneMapped={false} />
        </mesh>
      ) : (
        <Html center position={centre} className="scene-label warn" distanceFactor={22} zIndexRange={[5, 0]}>
          no exit defined
        </Html>
      )}
    </>
  );
}

/** Advances the clock, and asks the store for more frames when it runs low. */
function Driver() {
  const pump = useStore(s => s.pump);
  const onFrame = useStore(s => s.onFrame);
  const accumulator = useRef(0);

  useFrame((_, delta) => {
    const { playing, speed, replay } = useStore.getState();
    const dt = Math.min(delta, 0.1);

    if (replay) {
      // During a replay the clock shows trace states, stepped slowly enough to follow.
      if (replay.playing) {
        accumulator.current += dt;
        if (accumulator.current > 0.55) {
          accumulator.current = 0;
          const next = replay.index + 1;
          if (next > replay.trace.states.length) useStore.setState({ replay: { ...replay, playing: false } });
          else useStore.setState({ replay: { ...replay, index: next } });
        }
      }
      const state = useStore.getState().replay;
      const world = state ? (state.index === 0 ? state.trace.initial : state.trace.states[state.index - 1]) : null;
      if (world) {
        const prior = state!.index <= 1 ? state!.trace.initial : state!.trace.states[state!.index - 2];
        clock.previous = { ...(clock.previous ?? ({} as never)), tick: prior.tick, bodies: prior.bodies };
        clock.current = { ...(clock.current ?? ({} as never)), tick: world.tick, bodies: world.bodies };
        clock.alpha = Math.min(accumulator.current / 0.3, 1);
      }
      return;
    }

    if (playing) {
      pump();
      accumulator.current += dt * TICKS_PER_SECOND * speed;
      while (accumulator.current >= 1) {
        accumulator.current -= 1;
        const f = clock.queue.shift();
        if (!f) { accumulator.current = 0; break; }
        onFrame(f);
      }
      clock.alpha = accumulator.current;
    } else if (clock.alpha < 1) {
      clock.alpha = Math.min(clock.alpha + dt * 10, 1);
      if (clock.queue.length > 0 && clock.alpha >= 1) onFrame(clock.queue.shift()!);
    } else if (clock.queue.length > 0) {
      onFrame(clock.queue.shift()!);
    }
  });
  return null;
}

/** Lets ids in the current frame decide which meshes exist, without re-rendering each tick. */
function Bodies({ limit }: { limit: number }) {
  const tick = useStore(s => s.tick);
  const replayIndex = useStore(s => s.replay?.index);
  const signature = useRef("");
  const ids = useRef<number[]>([]);
  void tick; void replayIndex;
  const list = clock.current?.bodies.map(b => b.id) ?? [];
  const sig = list.join(",");
  if (sig !== signature.current) { signature.current = sig; ids.current = list; }
  return <>{ids.current.map(id => <BodyMesh key={id} id={id} limit={limit} />)}</>;
}

function Camera() {
  const { camera } = useThree();
  useEffect(() => { camera.lookAt(0, 0, 0); }, [camera]);
  return null;
}

function Space({ world }: { world: World }) {
  const select = useStore(s => s.select);
  const size = boundsSize(world.bounds);
  const floor = num(world.bounds.minY) - 0.02;
  return (
    <>
      <color attach="background" args={["#05070b"]} />
      <fog attach="fog" args={["#05070b", 45, 130]} />
      <ambientLight intensity={0.35} />
      <directionalLight position={[14, 26, 12]} intensity={1.1} />
      <pointLight position={[-14, -8, -10]} intensity={60} color="#4466ff" />
      <Stars radius={110} depth={40} count={2200} factor={3} saturation={0} fade speed={0.3} />
      <Grid position={[0, floor, 0]} args={[size[0], size[2]]} cellSize={1} sectionSize={5} cellThickness={0.4}
        sectionThickness={0.9} cellColor="#16323a" sectionColor="#1f6f6a" fadeDistance={80} infiniteGrid={false} />
      <Walls bounds={world.bounds} torus={world.laws.topology === "torus"} />
      {world.regions.map((r, i) => <RegionBox key={i} region={r} />)}
      {world.laws.fields.map((f, i) => <FieldBox key={i} field={f} />)}
      {world.portals.map((p, i) => <PortalRing key={i} portal={p} />)}
      <Bodies limit={num(world.laws.maxSpeed)} />
      <Driver />
      <Camera />
      <OrbitControls makeDefault enableDamping dampingFactor={0.08} minDistance={8} maxDistance={110} />
      <mesh visible={false} onClick={() => select(null)}>
        <sphereGeometry args={[200, 8, 8]} />
      </mesh>
      <EffectComposer multisampling={4}>
        <Bloom intensity={1.05} luminanceThreshold={0.62} luminanceSmoothing={0.2} mipmapBlur />
        <Vignette eskil={false} offset={0.22} darkness={0.75} />
      </EffectComposer>
    </>
  );
}

export function Universe() {
  const world = useStore(s => s.world);
  return (
    <Canvas camera={{ position: [31, 19, 40], fov: 38 }} dpr={[1, 2]} gl={{ antialias: true }}
      onPointerMissed={() => useStore.getState().select(null)}>
      {world && <Space world={world} />}
    </Canvas>
  );
}
