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

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Hilbertian fields

A field $K$ is Hilbertian if every irreducible polynomial $f(T, X)$ over $K(T)$ that is separable
in $X$ stays irreducible after some specialisation $T \mapsto a \in K$.

We state the condition for $f \in K[T][X]$ monic in $X$. Every separable Hilbert set of $K$
contains a set $H_K(f)$ for such an $f$, so this is equivalent to the definition through
separable Hilbert sets in [FJ08, Section 12.1].

*Reference:* [FJ08] M. D. Fried, M. Jarden, *Field Arithmetic*, 3rd ed., Springer, 2008,
Section 12.1.
-/

@[expose] public section

open Polynomial

namespace Field

/-- `K` is Hilbertian: for every monic irreducible `f ∈ K[T][X]` that is separable over `K(T)`,
there is `a ∈ K` such that `f(a, X)` is irreducible in `K[X]`. -/
def IsHilbertian (K : Type*) [Field K] : Prop :=
  ∀ f : K[X][X], f.Monic → Irreducible f → (f.map (algebraMap K[X] (RatFunc K))).Separable →
    ∃ a : K, Irreducible (f.map (evalRingHom a))

/-- An algebraically closed field is not Hilbertian: $X^2 + TX + T$ is irreducible by Eisenstein
at $T$, but every specialisation has degree $2$. -/
theorem not_isHilbertian_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] :
    ¬IsHilbertian K := by
  set f : K[X][X] := X ^ 2 + C X * X + C X
  have hdeg : f.natDegree = 2 := by
    simp only [f]; compute_degree!
  have hmonic : f.Monic := by
    simp only [f]; monicity!
  have hirr : Irreducible f := by
    refine IsEisensteinAt.irreducible (𝓟 := Ideal.span {X}) ?_
      ((Ideal.span_singleton_prime X_ne_zero).2 prime_X) hmonic.isPrimitive (by omega)
    refine hmonic.isEisensteinAt_of_mem_of_notMem ?_ (fun {n} hn ↦ ?_) ?_
    · rw [Ne, Ideal.span_singleton_eq_top]; exact not_isUnit_X
    · rw [hdeg] at hn
      interval_cases n <;> simp [f, coeff_X, coeff_C]
    · simp only [f, coeff_add, coeff_C_zero, coeff_X_pow, coeff_C_mul_X, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      norm_num
      intro h
      simpa using natDegree_le_of_dvd h X_ne_zero
  intro h
  obtain ⟨a, ha⟩ := h f hmonic hirr <| by
    have hirr' := (hmonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc K)).1 hirr
    refine (separable_iff_derivative_ne_zero hirr').2 fun h0 ↦ ?_
    have := congrArg (coeff · 0) h0
    simp [f] at this
  have := IsAlgClosed.degree_eq_one_of_irreducible K ha
  rw [degree_eq_natDegree ha.ne_zero, hmonic.natDegree_map, hdeg] at this
  norm_num at this

end Field
