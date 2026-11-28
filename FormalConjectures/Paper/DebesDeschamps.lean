/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Conjectures on absolute Galois groups from Dèbes–Deschamps

[DD97, §2] arranges classical conjectures on absolute Galois groups in a chain of implications.
This file states the Fried–Völklein conjecture **FrVo**. It implies Shafarevich's conjecture
**SHA**, stated as `Shafarevich.shafarevich`.

Mathlib has no free profinite groups. As for `Shafarevich.shafarevich`, we state "pro-free" with
Iwasawa's criterion [DD97, Th. 2.1], [FJ08, Cor. 24.8.3]: for a countable field $K$, $G_K$ is
pro-free if and only if every finite embedding problem for $G_K$ is properly solvable.

*References:*
- [DD97] P. Dèbes, B. Deschamps, *The regular inverse Galois problem over large fields*,
  Geometric Galois Actions 2, London Math. Soc. Lecture Note Ser. 243, Cambridge Univ. Press,
  1997, 119–138.
- [FJ08] M. D. Fried, M. Jarden, *Field Arithmetic*, 3rd ed., Springer, 2008.
- [FV92] M. D. Fried, H. Völklein, *The embedding problem over a Hilbertian PAC-field*,
  Ann. of Math. 135 (1992), 469–481.
-/

@[expose] public section

namespace DebesDeschamps

open EmbeddingProblem

/-- **Fried–Völklein conjecture** [DD97, §2.1.2], [FV92]. Let $K$ be a countable Hilbertian field
whose absolute Galois group $G_K$ is projective. Then $G_K$ is pro-free.

Projective means that every finite embedding problem for $G_K$ has a weak solution. Pro-free is
stated with Iwasawa's criterion: every finite embedding problem for $G_K$ has a proper solution.

This implies `Shafarevich.shafarevich`, since $\mathbb{Q}^{ab}$ is Hilbertian (Kuyk) and has
cohomological dimension at most $1$, so $G_{\mathbb{Q}^{ab}}$ is projective [DD97, §2.1.2]. -/
@[category research open, AMS 12 20]
theorem fried_volklein (K : Type) [Field K] [Countable K] (hK : Field.IsHilbertian K)
    (hproj : ∀ (A B : Type) [Group A] [Group B] (α : Field.absoluteGaloisGroup K →* A)
      (β : B →* A), IsFinite α β → ∃ γ, IsWeakSolution α β γ)
    {A B : Type} [Group A] [Group B] (α : Field.absoluteGaloisGroup K →* A) (β : B →* A)
    (h : IsFinite α β) : ∃ γ, IsProperSolution α β γ := by
  sorry

end DebesDeschamps
