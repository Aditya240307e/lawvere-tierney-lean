/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/

module

public import Mathlib.CategoryTheory.Sites.Sieves.Basic
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Sieves form a frame

The sieves on an object `X` form a complete lattice in Mathlib. Here it is shown to be a
Heyting algebra, hence a frame, with
`(S ⇨ T) f ↔ ∀ g, S (g ≫ f) → T (g ≫ f)`.
This is the implication of the internal logic of the presheaf topos, read off at stage `X`.
Pulling back along a morphism preserves all of the structure.

## Main results

* `Sieve.himp_apply`, `Sieve.compl_apply`: the implication and negation, on arrows.
* `Sieve.pullback_himp`, `Sieve.pullback_compl`: pullback is a Heyting algebra homomorphism.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace Sieve

variable {C : Type u} [Category.{v} C] {X : C}

/-- Heyting implication of sieves: `f` belongs to `S ⇨ T` when `S` and `T` agree on everything
that factors through `f`. -/
instance : HImp (Sieve X) where
  himp S T :=
    { arrows := fun Y f => ∀ ⦃Z⦄ (g : Z ⟶ Y), S (g ≫ f) → T (g ≫ f)
      downward_closed := by
        intro Y Z f hf g W h hS
        simpa using hf (h ≫ g) (by simpa using hS) }

theorem himp_apply {S T : Sieve X} {Y : C} (f : Y ⟶ X) :
    (S ⇨ T) f ↔ ∀ ⦃Z⦄ (g : Z ⟶ Y), S (g ≫ f) → T (g ≫ f) :=
  Iff.rfl

instance : HeytingAlgebra (Sieve X) where
  __ := (inferInstance : CompleteLattice (Sieve X))
  __ := (inferInstance : HImp (Sieve X))
  le_himp_iff S T U := by
    refine ⟨fun h Y f hf => ?_, fun h Y f hf Z g hg => ?_⟩
    · simpa using h f hf.1 (𝟙 _) (by simpa using hf.2)
    · exact h (g ≫ f) ⟨S.downward_closed hf g, hg⟩
  compl S := S ⇨ ⊥
  himp_bot _ := rfl

instance : Order.Frame (Sieve X) where
  __ := (inferInstance : CompleteLattice (Sieve X))
  __ := (inferInstance : HeytingAlgebra (Sieve X))

theorem compl_apply {S : Sieve X} {Y : C} (f : Y ⟶ X) :
    Sᶜ f ↔ ∀ ⦃Z⦄ (g : Z ⟶ Y), ¬ S (g ≫ f) :=
  Iff.rfl

theorem pullback_himp {Y : C} (f : Y ⟶ X) (S T : Sieve X) :
    (S ⇨ T).pullback f = S.pullback f ⇨ T.pullback f :=
  Sieve.ext fun Z g => by simp [himp_apply]

theorem pullback_compl {Y : C} (f : Y ⟶ X) (S : Sieve X) :
    Sᶜ.pullback f = (S.pullback f)ᶜ := by
  rw [← himp_bot, ← himp_bot, pullback_himp, pullback_bot]

end Sieve

end CategoryTheory
