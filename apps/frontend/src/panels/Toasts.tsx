import { useStore } from "../store";

export function Toasts() {
  const toasts = useStore(s => s.toasts);
  return (
    <div className="toasts" aria-live="polite">
      {toasts.map(t => (
        <div key={t.id} className={`toast ${t.kind}`}>
          <strong>{t.title}</strong>
          {t.detail && <span>{t.detail}</span>}
        </div>
      ))}
    </div>
  );
}
