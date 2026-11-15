# Mathathon #109 submission — tightening the 4th-order Trotter error bound

Caltech × SAIR Mathathon, Problem #109, submitted to the **Computation/Applied Math** track.

- `report.tex` — the self-contained report (no `\input`, no `.bib`, plots drawn by pgfplots from inline data)
- `report.pdf` — compiled from `report.tex` (`tectonic report.tex` or `pdflatex report.tex` twice)
- `lean/TrotterAnalytic/` — Lean 4 + Mathlib formalisation of the analytic argument
  (`lake exe cache get && lake build`; `lake env lean Axioms.lean` prints the axioms)
- `lean/TrotterAnalytic/TrotterAnalytic/S4Leading.lean` — kernel certificate of the leading term and processing identities (Lean core only; part of the same `lake build`)
- `slides.tex`, `slides.pdf` — Beamer slides (plots drawn from inline data)
- `explainer.md` — explainer readable after a first course in quantum computing

Code, data and full results: the parent folder `p109-trotter/` (`trotter/`, `scripts/`, `results/`, `tests/`).
