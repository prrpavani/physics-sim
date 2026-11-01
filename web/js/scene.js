// Draws worlds with three.js. No physics here: it only places meshes where a frame says bodies are,
// blending between two frames for smooth motion.

import * as THREE from "three";
import { OrbitControls } from "../vendor/OrbitControls.js";
import { vecNum, toNum } from "./num.js";

const TRAIL = 40;

const LOOKS = {
  solid: () => new THREE.MeshPhysicalMaterial({
    color: 0xbfe9ff, roughness: 0.08, metalness: 0, transparent: true, opacity: 0.82, clearcoat: 1,
  }),
  liquid: () => new THREE.MeshPhysicalMaterial({
    color: 0x2f8cff, roughness: 0.05, metalness: 0.1, transparent: true, opacity: 0.9, clearcoat: 1,
  }),
  gas: () => new THREE.MeshStandardMaterial({
    color: 0xf2f6ff, roughness: 1, transparent: true, opacity: 0.35, depthWrite: false,
  }),
  rubber: () => new THREE.MeshStandardMaterial({ color: 0xff6a3d, roughness: 0.45 }),
};
const GEOMETRY = {
  cube: new THREE.BoxGeometry(0.9, 0.9, 0.9),
  ball: new THREE.SphereGeometry(0.5, 32, 20),
  puff: new THREE.IcosahedronGeometry(0.75, 2),
};
const TRAIL_COLORS = { solid: 0x9fdcff, liquid: 0x2f8cff, gas: 0xdde6ff, rubber: 0xff6a3d };

const lookOf = b => (b.material === "rubber" ? "rubber" : b.phase);
const shapeOf = look => (look === "solid" ? "cube" : look === "gas" ? "puff" : "ball");

export function createScene(canvas) {
  const renderer = new THREE.WebGLRenderer({ canvas, antialias: true });
  renderer.setPixelRatio(window.devicePixelRatio);
  renderer.shadowMap.enabled = true;
  renderer.toneMapping = THREE.ACESFilmicToneMapping;

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x0b0e14);
  scene.fog = new THREE.Fog(0x0b0e14, 40, 90);

  const camera = new THREE.PerspectiveCamera(45, 1, 0.1, 200);
  camera.position.set(22, 18, 26);
  const controls = new OrbitControls(camera, canvas);
  controls.target.set(0, 5, 0);
  controls.enableDamping = true;
  controls.maxPolarAngle = Math.PI * 0.495;

  scene.add(new THREE.HemisphereLight(0xbcd4ff, 0x1a1408, 0.9));
  const sun = new THREE.DirectionalLight(0xffffff, 1.6);
  sun.position.set(12, 30, 8);
  sun.castShadow = true;
  sun.shadow.mapSize.set(2048, 2048);
  Object.assign(sun.shadow.camera, { left: -15, right: 15, top: 15, bottom: -15 });
  scene.add(sun);

  const box = new THREE.Group();
  scene.add(box);
  const bodies = new Map(); // id → { mesh, look, trail, line }
  let selected = null;

  function setBounds(bounds) {
    box.clear();
    const lo = vecNum(bounds.min), hi = vecNum(bounds.max);
    const size = hi.map((h, i) => h - lo[i]);
    const mid = hi.map((h, i) => (h + lo[i]) / 2);
    const edges = new THREE.LineSegments(
      new THREE.EdgesGeometry(new THREE.BoxGeometry(...size)),
      new THREE.LineBasicMaterial({ color: 0x5b7cff, transparent: true, opacity: 0.55 }));
    edges.position.set(...mid);
    box.add(edges);
    const floor = new THREE.Mesh(new THREE.PlaneGeometry(size[0], size[2]),
      new THREE.MeshStandardMaterial({ color: 0x141a26, roughness: 0.9 }));
    floor.rotation.x = -Math.PI / 2;
    floor.position.set(mid[0], lo[1] - 0.001, mid[2]);
    floor.receiveShadow = true;
    box.add(floor);
    const grid = new THREE.GridHelper(Math.max(size[0], size[2]), Math.max(size[0], size[2]), 0x2a3550, 0x1c2436);
    grid.position.set(mid[0], lo[1], mid[2]);
    box.add(grid);
  }

  function bodyView(b) {
    const look = lookOf(b);
    let view = bodies.get(b.id);
    if (view && view.look === look) return view;
    if (view) scene.remove(view.mesh);
    const mesh = new THREE.Mesh(GEOMETRY[shapeOf(look)], LOOKS[look]());
    mesh.castShadow = look !== "gas";
    mesh.userData.id = b.id;
    scene.add(mesh);
    if (!view) {
      const line = new THREE.Line(new THREE.BufferGeometry(),
        new THREE.LineBasicMaterial({ transparent: true, opacity: 0.45 }));
      scene.add(line);
      view = { trail: [], line };
    }
    view.line.material.color.setHex(TRAIL_COLORS[look]);
    Object.assign(view, { mesh, look, pop: 1 });
    bodies.set(b.id, view);
    return view;
  }

  /** Draw the world between frames `a` and `b`, at fraction `t` of the way. */
  function show(a, b, t) {
    const before = new Map(a.bodies.map(x => [x.id, x]));
    const alive = new Set();
    for (const body of b.bodies) {
      alive.add(body.id);
      const view = bodyView(body);
      const p1 = vecNum(body.position);
      const prev = before.get(body.id);
      const p0 = prev ? vecNum(prev.position) : p1;
      const p = p0.map((x, i) => x + (p1[i] - x) * t);
      view.mesh.position.set(...p);
      // A phase change makes the body pop.
      view.pop = Math.max(0, view.pop - 0.05);
      const s = (1 + 0.5 * view.pop) * (body.material === "rubber" ? 1 : 0.8 + 0.1 * Math.cbrt(toNum(body.mass)));
      view.mesh.scale.setScalar(s);
      if (view.look === "gas") view.mesh.rotation.y += 0.01;
      view.mesh.material.emissive?.setHex(body.id === selected ? 0x334477 : 0x000000);
      const last = view.trail[view.trail.length - 1];
      if (!last || Math.hypot(...p.map((x, i) => x - last[i])) > 0.15) {
        view.trail.push(p);
        if (view.trail.length > TRAIL) view.trail.shift();
        // A geometry can't grow in place, so make a new one.
        view.line.geometry.dispose();
        view.line.geometry = new THREE.BufferGeometry().setFromPoints(view.trail.map(q => new THREE.Vector3(...q)));
      }
    }
    for (const [id, view] of bodies) {
      if (!alive.has(id)) { scene.remove(view.mesh); scene.remove(view.line); bodies.delete(id); }
    }
  }

  function clearTrails() {
    for (const view of bodies.values()) {
      view.trail = [];
      view.line.geometry.dispose();
      view.line.geometry = new THREE.BufferGeometry();
    }
  }

  const raycaster = new THREE.Raycaster();
  /** The id of the body under a screen point, or null. */
  function pick(clientX, clientY) {
    const r = canvas.getBoundingClientRect();
    raycaster.setFromCamera(new THREE.Vector2(
      ((clientX - r.left) / r.width) * 2 - 1, -((clientY - r.top) / r.height) * 2 + 1), camera);
    const hit = raycaster.intersectObjects([...bodies.values()].map(v => v.mesh))[0];
    return hit ? hit.object.userData.id : null;
  }

  function render() {
    const { clientWidth: w, clientHeight: h } = canvas;
    if (canvas.width !== Math.round(w * renderer.getPixelRatio()) || canvas.height !== Math.round(h * renderer.getPixelRatio())) {
      renderer.setSize(w, h, false);
      camera.aspect = w / h;
      camera.updateProjectionMatrix();
    }
    controls.update();
    renderer.render(scene, camera);
  }

  return { setBounds, show, clearTrails, pick, render, select: id => { selected = id; } };
}
