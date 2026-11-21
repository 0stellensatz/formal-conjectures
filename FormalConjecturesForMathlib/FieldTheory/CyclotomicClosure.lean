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

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The maximal cyclotomic extension

`IntermediateField.cyclotomicClosure K` is the subfield $K(\mu_\infty)$ of `AlgebraicClosure K`
generated over `K` by all roots of unity. For `K = ℚ` it is the maximal abelian extension
$\mathbb{Q}^{ab}$ of `ℚ`, by the Kronecker–Weber theorem.
-/

@[expose] public noncomputable section

namespace IntermediateField

variable (K : Type*) [Field K]

/-- The subfield of `AlgebraicClosure K` generated over `K` by all roots of unity. -/
def cyclotomicClosure : IntermediateField K (AlgebraicClosure K) :=
  adjoin K {x | ∃ n ≠ 0, x ^ n = 1}

variable {K} in
theorem mem_cyclotomicClosure {x : AlgebraicClosure K} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) :
    x ∈ cyclotomicClosure K :=
  subset_adjoin _ _ ⟨n, hn, hx⟩

end IntermediateField
