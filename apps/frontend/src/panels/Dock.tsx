import { useState } from "react";
import { UniversesTab } from "./UniversesTab";
import { LawsTab } from "./LawsTab";
import { ForceLab } from "./ForceLab";
import { RulesTab } from "./RulesTab";
import { ObjectsTab } from "./ObjectsTab";
import { SpaceTab } from "./SpaceTab";

const TABS = [
  { id: "universes", label: "Universes", render: () => <UniversesTab /> },
  { id: "laws", label: "Laws", render: () => <LawsTab /> },
  { id: "force", label: "Force Lab", render: () => <ForceLab /> },
  { id: "rules", label: "Rules", render: () => <RulesTab /> },
  { id: "objects", label: "Objects", render: () => <ObjectsTab /> },
  { id: "space", label: "Space", render: () => <SpaceTab /> },
] as const;

export function Dock() {
  const [tab, setTab] = useState<(typeof TABS)[number]["id"]>("universes");
  const [open, setOpen] = useState(true);
  const current = TABS.find(t => t.id === tab)!;
  return (
    <aside className={`dock ${open ? "" : "closed"}`}>
      <nav className="dock-tabs" aria-label="Universe controls">
        {TABS.map(t => (
          <button key={t.id} type="button" aria-pressed={open && tab === t.id}
            onClick={() => { if (open && tab === t.id) setOpen(false); else { setTab(t.id); setOpen(true); } }}>
            {t.label}
          </button>
        ))}
      </nav>
      {open && <div className="dock-body">{current.render()}</div>}
    </aside>
  );
}
