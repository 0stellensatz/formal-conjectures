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
public import FormalConjectures.Wikipedia.InverseGalois

/-!
# Conjectures on absolute Galois groups from Dèbes–Deschamps

[DD97, §2] arranges classical conjectures on absolute Galois groups in a chain of implications.
This file states the parts
$$\textbf{Split EP}/K(T) \iff \textbf{Split EP}/K_{hilb.} \implies \textbf{FrVo}
  \implies \textbf{SHA},$$
$$\textbf{RIGP}/K(T) \implies \textbf{IGP}/K_{hilb.} \implies \textbf{IGP}, \qquad
  \textbf{Split EP}/K_{hilb.} \implies \textbf{IGP}/K_{hilb.},$$
where **SHA** is Shafarevich's conjecture `Shafarevich.shafarevich` and **IGP** is the inverse
Galois problem `InverseGalois.inverse_galois_problem`.

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
- [Po96] F. Pop, *Embedding problems over large fields*, Ann. of Math. 144 (1996), 1–35.
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

/-- **Split embedding problem conjecture over Hilbertian fields** [DD97, §2.1.2]. Let $K$ be a
Hilbertian field. Then every finite split embedding problem for $G_K$ has a proper solution.

The embedding problem $(\alpha, \beta)$ is split if $\beta : B \to A$ has a group-theoretic
section $s$.

This implies `fried_volklein`: by projectivity and the weak-to-split reduction, every finite
embedding problem reduces to a split one [DD97, §2.1.2]. The case $A = 1$ says that every finite
group is a Galois group over $K$, which is `igp_hilbertian`. Pop proved the conjecture for ample Hilbertian fields [Po96]. -/
@[category research open, AMS 12 20]
theorem split_ep_hilbertian (K : Type*) [Field K] (hK : Field.IsHilbertian K)
    {A B : Type} [Group A] [Group B] (α : Field.absoluteGaloisGroup K →* A) (β : B →* A)
    (h : IsFinite α β) (s : A →* B) (hs : β.comp s = .id A) : ∃ γ, IsProperSolution α β γ := by
  sorry

/-- **Split embedding problem conjecture over $K(T)$** [DD97, §2.1.2]. Let $K$ be any field. Then
every finite split embedding problem for $G_{K(T)}$ has a proper solution.

This is equivalent to `split_ep_hilbertian`. The field $K(T)$ is Hilbertian, and a proper
solution over $K(T)$ specialises to one over a Hilbertian $K$ [DD97, §2.1.2]. -/
@[category research open, AMS 12 20]
theorem split_ep_ratFunc (K : Type*) [Field K]
    {A B : Type} [Group A] [Group B] (α : Field.absoluteGaloisGroup (RatFunc K) →* A)
    (β : B →* A) (h : IsFinite α β) (s : A →* B) (hs : β.comp s = .id A) :
    ∃ γ, IsProperSolution α β γ := by
  sorry

/-- **Inverse Galois problem over Hilbertian fields** [DD97, §2.1.1]. Let $K$ be a Hilbertian
field. Then every finite group is the Galois group of a Galois extension of $K$.

This implies `InverseGalois.inverse_galois_problem`, since $\mathbb{Q}$ is Hilbertian by
Hilbert's irreducibility theorem. -/
@[category research open, AMS 12 20]
theorem igp_hilbertian (K : Type*) [Field K] (hK : Field.IsHilbertian K)
    (G : Type*) [Group G] [Finite G] : InverseGalois.IsRealizable K G := by
  sorry

/-- **Regular inverse Galois problem** [DD97, §2.1.1]. Let $K$ be any field. Then every finite
group $G$ is the Galois group of a Galois extension $E/K(T)$ that is regular, that is, $K$ is
algebraically closed in $E$.

Every finite extension of $K(T)$ embeds in an algebraic closure of $K(T)$, so we take $E$ inside
`AlgebraicClosure (RatFunc K)`.

This implies `igp_hilbertian` by specialising $T$ [DD97, §2.1.1]. A regular realisation over $K$
gives one over every extension of $K$, so it suffices to treat the prime fields [DD97, §1]. -/
@[category research open, AMS 12 20]
theorem rigp_ratFunc (K : Type*) [Field K] (G : Type*) [Group G] [Finite G] :
    ∃ E : IntermediateField (RatFunc K) (AlgebraicClosure (RatFunc K)),
      IsGalois (RatFunc K) E ∧ Nonempty (G ≃* (E ≃ₐ[RatFunc K] E)) ∧
      ∀ x : E, IsAlgebraic K x → x ∈ (algebraMap K E).range := by
  sorry

end DebesDeschamps
