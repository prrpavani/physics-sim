import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

// The built UI goes to web/, which the Lean server serves. `npm run dev` proxies the API to it.
export default defineConfig({
  plugins: [react()],
  base: "/",
  build: {
    outDir: "../../web",
    emptyOutDir: true,
    chunkSizeWarningLimit: 2000,
    assetsInlineLimit: 0,
  },
  server: {
    port: 5173,
    proxy: { "/api": "http://127.0.0.1:8787" },
  },
});
