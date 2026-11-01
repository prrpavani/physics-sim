// Draws the universe. Every position comes from a state the Lean model produced. The scene only blends
// between two states for smooth motion. No physics here.

import { Canvas, useFrame } from "@react-three/fiber";
import { Grid, OrbitControls, Stars } from "@react-three/drei";
import { Bloom, EffectComposer, Vignette } from "@react-three/postprocessing";
import { useMemo, useRef } from "react";
import * as THREE from "three";
import type { Body, Bounds } from "../api";
import { num } from "../lib/num";
import { clock, TICKS_PER_SECOND, useStore } from "../store";

type V3 = [number, number, number];
const TRAIL_LENGTH = 70;
const REPLAY_SECONDS_PER_STEP = 0.35;

const drawOf = (b: Body): V3 => (b.draw as V3 | undefined) ?? [num(b.position.x), num(b.position.y), num(b.position.z)];
const velocityOf = (b: Body): V3 => (b.drawVelocity as V3 | undefined) ?? [num(b.velocity.x), num(b.velocity.y), num(b.velocity.z)];

function drawn(id: number): { position: V3; velocity: V3 } | null {
  const now = clock.current?.bodies.find(b => b.id === id);
  if (!now) return null;
  const prev = clock.previous?.bodies.find(b => b.id === id);
  const end = drawOf(now);
  if (!prev) return { position: end, velocity: velocityOf(now) };
  const start = drawOf(prev);
  const a = clock.alpha;
  return {
    position: [start[0] + (end[0] - start[0]) * a, start[1] + (end[1] - start[1]) * a, start[2] + (end[2] - start[2]) * a],
    velocity: velocityOf(now),
  };
}

function Sphere({ id, radius, limit }: { id: number; radius: number; limit: number }) {
  const group = useRef<THREE.Group>(null);
  const mat = useRef<THREE.MeshStandardMaterial>(null);
  const line = useRef<THREE.BufferGeometry>(null);
  const trail = useMemo(() => new Float32Array(TRAIL_LENGTH * 3), []);
  const colors = useMemo(() => new Float32Array(TRAIL_LENGTH * 3), []);
  const filled = useRef(0);
  const calm = useMemo(() => new THREE.Color("#c8fff0"), []);
  const hot = useMemo(() => new THREE.Color("#ff2d55"), []);

  useFrame(() => {
    const d = drawn(id);
    if (!d || !group.current) return;
    const [x, y, z] = d.position;
    group.current.position.set(x, y, z);
    const speed = Math.max(...d.velocity.map(Math.abs));
    const over = speed > limit + 1e-6;
    const color = over ? hot : calm;
    if (mat.current) {
      mat.current.color.copy(color);
      mat.current.emissive.copy(color);
      mat.current.emissiveIntensity = over ? 3 : 0.2 + Math.min(speed / limit, 1) * 1.6;
    }
    trail.copyWithin(3, 0, (TRAIL_LENGTH - 1) * 3);
    trail[0] = x; trail[1] = y; trail[2] = z;
    filled.current = Math.min(filled.current + 1, TRAIL_LENGTH);
    for (let i = 0; i < TRAIL_LENGTH; i++) {
      const fade = Math.pow(1 - i / TRAIL_LENGTH, 2);
      colors[i * 3] = color.r * fade; colors[i * 3 + 1] = color.g * fade; colors[i * 3 + 2] = color.b * fade;
    }
    if (line.current) {
      line.current.attributes.position.needsUpdate = true;
      line.current.attributes.color.needsUpdate = true;
      line.current.setDrawRange(0, filled.current);
    }
  });

  return (
    <>
      <group ref={group}>
        <mesh>
          <sphereGeometry args={[radius, 32, 20]} />
          <meshStandardMaterial ref={mat} metalness={0.2} roughness={0.25} toneMapped={false} />
        </mesh>
      </group>
      <line>
        <bufferGeometry ref={line}>
          <bufferAttribute attach="attributes-position" args={[trail, 3]} />
          <bufferAttribute attach="attributes-color" args={[colors, 3]} />
        </bufferGeometry>
        <lineBasicMaterial vertexColors transparent opacity={0.9} toneMapped={false} />
      </line>
    </>
  );
}

/** The walls. Calm while the promises hold, alarmed when one has broken. */
function Walls({ bounds }: { bounds: Bounds }) {
  const locked = useStore(s => s.locked);
  const alarm = useStore(s => s.broken.speedLimit || s.broken.staysInside || !!s.replay);
  const material = useRef<THREE.LineBasicMaterial>(null);
  const size: V3 = [num(bounds.maxX) - num(bounds.minX), num(bounds.maxY) - num(bounds.minY), num(bounds.maxZ) - num(bounds.minZ)];
  const edges = useMemo(() => new THREE.EdgesGeometry(new THREE.BoxGeometry(...size)), [size[0], size[1], size[2]]);
  const color = alarm ? "#ff2d55" : locked ? "#35f0c4" : "#ffb74d";
  useFrame(({ clock: c }) => {
    const pulse = alarm ? 1.8 + Math.sin(c.elapsedTime * 7) * 1.2 : 1.2 + Math.sin(c.elapsedTime * 1.5) * 0.2;
    material.current?.color.set(color).multiplyScalar(pulse);
  });
  return (
    <group position={[(num(bounds.minX) + num(bounds.maxX)) / 2, (num(bounds.minY) + num(bounds.maxY)) / 2, (num(bounds.minZ) + num(bounds.maxZ)) / 2]}>
      <lineSegments geometry={edges}><lineBasicMaterial ref={material} toneMapped={false} /></lineSegments>
      <mesh>
        <boxGeometry args={size} />
        <meshBasicMaterial color={color} transparent opacity={0.018} side={THREE.BackSide} depthWrite={false} />
      </mesh>
    </group>
  );
}

/** Advances the clock each frame, and asks for more states when it runs low. */
function Driver() {
  const accumulator = useRef(0);
  useFrame((_, delta) => {
    const s = useStore.getState();
    const dt = Math.min(delta, 0.1);
    if (s.replay) {
      const { trace } = s.replay;
      if (s.replay.playing) {
        accumulator.current += dt;
        if (accumulator.current > REPLAY_SECONDS_PER_STEP) {
          accumulator.current = 0;
          if (s.replay.index >= trace.states.length) useStore.setState({ replay: { ...s.replay, playing: false } });
          else useStore.setState({ replay: { ...s.replay, index: s.replay.index + 1 } });
        }
      }
      const index = useStore.getState().replay?.index ?? 0;
      const worldAt = (i: number) => (i <= 0 ? trace.start : trace.states[i - 1]);
      const none = { staysInside: false, speedLimit: false };
      clock.previous = { tick: worldAt(index - 1).tick, bodies: worldAt(index - 1).bodies, broken: none };
      clock.current = { tick: worldAt(index).tick, bodies: worldAt(index).bodies, broken: none };
      clock.alpha = Math.min(accumulator.current / (REPLAY_SECONDS_PER_STEP * 0.8), 1);
      return;
    }
    if (s.playing) {
      s.pump();
      accumulator.current += dt * TICKS_PER_SECOND;
      while (accumulator.current >= 1) {
        accumulator.current -= 1;
        const f = clock.queue.shift();
        if (!f) { accumulator.current = 0; break; }
        s.onFrame(f);
      }
      clock.alpha = accumulator.current;
    } else if (clock.alpha < 1) {
      clock.alpha = Math.min(clock.alpha + dt * 10, 1);
    } else if (clock.queue.length > 0) {
      s.onFrame(clock.queue.shift()!);
    }
  });
  return null;
}

function Spheres({ limit }: { limit: number }) {
  useStore(s => s.tick);
  useStore(s => s.replay?.index);
  const bodies = clock.current?.bodies ?? [];
  return <>{bodies.map(b => {
    const radius = num(b.radius);
    return <Sphere key={`${b.id}-${radius}`} id={b.id} radius={radius} limit={limit} />;
  })}</>;
}

export function Universe() {
  const world = useStore(s => s.world);
  return (
    <Canvas camera={{ position: [31, 19, 40], fov: 38 }} dpr={[1, 2]} gl={{ antialias: true }}>
      {world && (
        <>
          <color attach="background" args={["#05070b"]} />
          <ambientLight intensity={0.35} />
          <directionalLight position={[14, 26, 12]} intensity={1.1} />
          <Stars radius={110} depth={40} count={2200} factor={3} saturation={0} fade speed={0.3} />
          <Grid position={[0, num(world.bounds.minY) - 0.02, 0]} args={[20, 20]} cellSize={1} sectionSize={5} cellThickness={0.4}
            sectionThickness={0.9} cellColor="#16323a" sectionColor="#1f6f6a" fadeDistance={80} />
          <Walls bounds={world.bounds} />
          <Spheres limit={num(world.laws.maxSpeed)} />
          <Driver />
          <OrbitControls makeDefault enableDamping dampingFactor={0.08} minDistance={8} maxDistance={110} />
          <EffectComposer multisampling={4}>
            <Bloom intensity={1.05} luminanceThreshold={0.62} luminanceSmoothing={0.2} mipmapBlur />
            <Vignette eskil={false} offset={0.22} darkness={0.75} />
          </EffectComposer>
        </>
      )}
    </Canvas>
  );
}
