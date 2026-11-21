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

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Basic

/-!
# Finite embedding problems

A finite embedding problem for a topological group `G` is a pair `(α, β)` of a continuous
epimorphism `α : G → A` onto a finite group and an epimorphism `β : B → A` of finite groups.
A solution is a continuous homomorphism `γ : G → B` with `β ∘ γ = α`. It is proper if `γ` is
surjective.

Finite groups carry the discrete topology. For a topological group, a homomorphism to a discrete
group is continuous if and only if its kernel is open. We state continuity in that form.

*Reference:* M. D. Fried, M. Jarden, *Field Arithmetic*, 3rd ed., Springer, 2008, Section 22.2.
-/

@[expose] public section

namespace EmbeddingProblem

variable {G A B : Type*} [Group G] [TopologicalSpace G] [Group A] [Group B]

/-- `(α, β)` is a finite embedding problem for `G`: `B` is finite, `α : G → A` is surjective with
open kernel, and `β : B → A` is surjective. -/
def IsFinite (α : G →* A) (β : B →* A) : Prop :=
  Finite B ∧ IsOpen (α.ker : Set G) ∧ Function.Surjective α ∧ Function.Surjective β

/-- `γ` is a (weak) solution of the embedding problem `(α, β)`: it has open kernel and
`β ∘ γ = α`. -/
def IsWeakSolution (α : G →* A) (β : B →* A) (γ : G →* B) : Prop :=
  IsOpen (γ.ker : Set G) ∧ β.comp γ = α

/-- `γ` is a proper solution of the embedding problem `(α, β)`: a surjective weak solution. -/
def IsProperSolution (α : G →* A) (β : B →* A) (γ : G →* B) : Prop :=
  IsWeakSolution α β γ ∧ Function.Surjective γ

/-- Every group has finite embedding problems: the trivial map onto `Unit` and any finite `B`. -/
theorem isFinite_one [Finite B] : IsFinite (1 : G →* Unit) (1 : B →* Unit) :=
  ⟨‹_›, by simp, fun _ ↦ ⟨1, rfl⟩, fun _ ↦ ⟨1, rfl⟩⟩

/-- An embedding problem with `β = id` has the proper solution `α`. -/
theorem isProperSolution_id {α : G →* A} (hα : IsOpen (α.ker : Set G))
    (hα' : Function.Surjective α) : IsProperSolution α (MonoidHom.id A) α :=
  ⟨⟨hα, MonoidHom.id_comp α⟩, hα'⟩

/-- The trivial group has no proper solution onto a nontrivial group. So "every finite embedding
problem is properly solvable" is not a vacuous property. -/
theorem not_isProperSolution_of_subsingleton [Subsingleton G] [Nontrivial B]
    (α : G →* A) (β : B →* A) (γ : G →* B) : ¬IsProperSolution α β γ := fun h ↦ by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne B
  obtain ⟨g, rfl⟩ := h.2 x
  obtain ⟨g', rfl⟩ := h.2 y
  exact hxy (congrArg γ (Subsingleton.elim g g'))

end EmbeddingProblem
