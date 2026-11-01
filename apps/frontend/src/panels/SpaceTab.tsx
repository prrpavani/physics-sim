import { useState } from "react";
import type { Portal, PortalEffect, Region } from "../../../../shared/types/paradox";
import { boundsAround, frac, num, vec } from "../lib/num";
import { useStore } from "../store";
import { LawSlider, Select } from "./common";

const COLORS = ["red", "dodgerblue", "limegreen", "gold", "orchid"];
type EffectKind = PortalEffect["type"];

export function SpaceTab() {
  const world = useStore(s => s.world);
  const send = useStore(s => s.send);
  const [regionColor, setRegionColor] = useState("red");
  const [timeScale, setTimeScale] = useState(1);
  const [effect, setEffect] = useState<EffectKind>("scale");
  const [factor, setFactor] = useState(2);
  const [withExit, setWithExit] = useState(true);
  const [fieldUp, setFieldUp] = useState(20);
  if (!world) return null;

  const addRegion = () => {
    const name = `${regionColor} zone ${world.regions.length + 1}`;
    const region: Region = {
      name, color: regionColor,
      box: boundsAround(Math.random() * 8 - 4, Math.random() * 8 - 4, Math.random() * 8 - 4, 3),
      timeScale: frac(timeScale),
    };
    send({ type: "addRegion", region });
  };
  const addPortal = () => {
    const eff: PortalEffect = effect === "scale" ? { type: "scale", factor: frac(factor) } : { type: effect };
    const portal: Portal = {
      entrance: boundsAround(Math.random() * 10 - 5, -7, Math.random() * 10 - 5, 2.5),
      exit: withExit ? vec(Math.random() * 10 - 5, 6, Math.random() * 10 - 5) : null,
      effect: eff,
    };
    send({ type: "addPortal", portal });
  };

  return (
    <div className="tab">
      <h2>Regions, portals, fields</h2>
      <p className="lede">Reshape space. Where regions overlap, the first one decides the time rate. Where fields overlap, they add.</p>

      <h3>Region</h3>
      <div className="color-row" role="group" aria-label="Region colour">
        {COLORS.map(c => (
          <button key={c} type="button" className="swatch" aria-label={c} aria-pressed={regionColor === c} style={{ background: c }} onClick={() => setRegionColor(c)} />
        ))}
      </div>
      <LawSlider label="Time inside" value={timeScale} min={0} max={3} step={0.05} unit="×" onCommit={setTimeScale} hint="0 stops motion inside. 1 is normal time." />
      <button type="button" onClick={addRegion}>Add a region</button>

      <h3>Portal</h3>
      <div className="field">
        <label>What it does to velocity</label>
        <Select<EffectKind> label="Portal effect" value={effect} onChange={setEffect} options={[
          { value: "none", label: "Nothing" }, { value: "reverse", label: "Reverse it" },
          { value: "rotate", label: "Turn it" }, { value: "scale", label: "Multiply it" },
        ]} />
      </div>
      {effect === "scale" && (
        <LawSlider label="Multiply by" value={factor} min={-3} max={100} step={0.5} onCommit={setFactor}
          danger={v => (Math.abs(v) > 1 ? "Can add speed. Protected mode repairs this to a factor of 1." : null)} />
      )}
      <label className="check"><input type="checkbox" checked={withExit} onChange={e => setWithExit(e.target.checked)} /> Has a destination</label>
      {!withExit && <small className="warn-text">The inspector will report this as missing behaviour.</small>}
      <button type="button" onClick={addPortal}>Add a portal</button>

      <h3>Gravity field</h3>
      <LawSlider label="Pull upward inside" value={fieldUp} min={-60} max={60} step={1} unit=" m/s²" onCommit={setFieldUp} />
      <button type="button" onClick={() => send({
        type: "addField",
        field: { region: boundsAround(Math.random() * 8 - 4, Math.random() * 8 - 4, Math.random() * 8 - 4, 4), acceleration: vec(0, fieldUp, 0) },
      })}>Add a field</button>

      <h3>In this universe</h3>
      <ul className="plain">
        <li>{world.regions.length} regions <button type="button" className="link" onClick={() => send({ type: "clearRegions" })}>clear</button></li>
        <li>{world.portals.length} portals <button type="button" className="link" onClick={() => send({ type: "clearPortals" })}>clear</button></li>
        <li>{world.laws.fields.length} fields <button type="button" className="link" onClick={() => send({ type: "clearFields" })}>clear</button></li>
        <li>Box from {num(world.bounds.minX)} to {num(world.bounds.maxX)} on each axis</li>
      </ul>
    </div>
  );
}
