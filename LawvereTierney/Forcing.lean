/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/

module

public import LawvereTierney.Heyting
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subfunctor.Sieves
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Kripke–Joyal forcing in the presheaf topos

For a presheaf `F`, the subpresheaves of `F` are the propositions about a variable ranging over
`F`, and `x ∈ A.obj U` reads "`U` forces `A(x)`". This file shows that subpresheaves form a frame
whose operations are the Kripke–Joyal clauses:

* `⊓` and `⊤` are computed stage by stage;
* `A ⇨ B` holds at `x` when `B` holds at every later stage where `A` does;
* `Aᶜ` holds at `x` when `A` holds at no later stage;
* `∃` along a map is its image (`Subfunctor.image`), and `∀` is the right adjoint of pullback
  (`Subfunctor.forall`).

Taking the sieve of all arrows along which a section lies in `A` turns each of these into the
corresponding operation on sieves (`Subfunctor.sieveOfSection_himp` and the lemmas around it), so at
each stage the logic is that of the Heyting algebra of sieves. The sheaf semantics for a
Lawvere–Tierney topology is in `LawvereTierney.SheafForcing`.

## Main definitions

* `Subfunctor.forall`: universal quantification along a morphism.

## Main results

* `Subfunctor.mem_himp_iff`, `Subfunctor.mem_compl_iff`: the clauses for `⇨` and `¬`.
* `Subfunctor.le_forall_iff`: `∀` is right adjoint to pullback.
* `Subfunctor.sieveOfSection_himp`, `Subfunctor.sieveOfSection_compl`: forcing commutes with the
  connectives.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite

namespace Subfunctor

variable {D : Type u} [Category.{v} D] {F F' : D ⥤ Type w}

/-- Heyting implication of subfunctors: `x` satisfies `A ⇨ B` when `B` holds at every later stage
at which `A` does. -/
instance : HImp (Subfunctor F) where
  himp A B :=
    { obj U := {x | ∀ ⦃V⦄ (f : U ⟶ V), F.map f x ∈ A.obj V → F.map f x ∈ B.obj V}
      map := by
        intro U U' g x hx V f hA
        have := hx (g ≫ f)
        simp only [Functor.map_comp_apply] at this
        exact this hA }

theorem mem_himp_iff {A B : Subfunctor F} {U : D} {x : F.obj U} :
    x ∈ (A ⇨ B).obj U ↔ ∀ ⦃V⦄ (f : U ⟶ V), F.map f x ∈ A.obj V → F.map f x ∈ B.obj V :=
  Iff.rfl

instance : HeytingAlgebra (Subfunctor F) where
  __ := (inferInstance : CompleteLattice (Subfunctor F))
  __ := (inferInstance : HImp (Subfunctor F))
  le_himp_iff A B C := by
    refine ⟨fun h U x hx => ?_, fun h U x hxA V f hxB => ?_⟩
    · simpa using h U hx.1 (𝟙 U) (by simpa using hx.2)
    · exact h V ⟨A.map f hxA, hxB⟩
  compl A := A ⇨ ⊥
  himp_bot _ := rfl

instance : Order.Frame (Subfunctor F) where
  __ := (inferInstance : CompleteLattice (Subfunctor F))
  __ := (inferInstance : HeytingAlgebra (Subfunctor F))

theorem mem_compl_iff {A : Subfunctor F} {U : D} {x : F.obj U} :
    x ∈ Aᶜ.obj U ↔ ∀ ⦃V⦄ (f : U ⟶ V), F.map f x ∉ A.obj V :=
  Iff.rfl

/-- Universal quantification along a morphism `p : F ⟶ F'`: `x'` satisfies `A.forall p` when `A`
holds of every `y` that `p` sends to a restriction of `x'`. It is right adjoint to `preimage`. -/
def «forall» (A : Subfunctor F) (p : F ⟶ F') : Subfunctor F' where
  obj U := {x | ∀ ⦃V⦄ (g : U ⟶ V) (y : F.obj V), p.app V y = F'.map g x → y ∈ A.obj V}
  map := by
    intro U U' g x hx V h y hy
    refine hx (g ≫ h) y ?_
    simpa [Functor.map_comp_apply] using hy

theorem le_forall_iff {A : Subfunctor F} {p : F ⟶ F'} {G : Subfunctor F'} :
    G ≤ A.forall p ↔ G.preimage p ≤ A := by
  refine ⟨fun h U y hy => ?_, fun h U x hx V g y hy => ?_⟩
  · exact h U hy (𝟙 U) y (by simp)
  · exact h V (by simpa [hy] using G.map g hx)

section SieveOfSection

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} (A B : Subfunctor F)

theorem sieveOfSection_map {X Y : C} (f : Y ⟶ X) (x : F.obj (op X)) :
    A.sieveOfSection (F.map f.op x) = (A.sieveOfSection x).pullback f :=
  Sieve.ext fun Z g => by simp [Subfunctor.sieveOfSection]

variable {A B}

theorem sieveOfSection_eq_top_iff {X : Cᵒᵖ} {x : F.obj X} :
    A.sieveOfSection x = ⊤ ↔ x ∈ A.obj X := by
  rw [← Sieve.id_mem_iff_eq_top]
  simp [Subfunctor.sieveOfSection]

variable (A B) {X : Cᵒᵖ} (x : F.obj X)

@[simp]
theorem sieveOfSection_top : (⊤ : Subfunctor F).sieveOfSection x = ⊤ :=
  Sieve.ext fun _ _ => iff_of_true trivial trivial

@[simp]
theorem sieveOfSection_bot : (⊥ : Subfunctor F).sieveOfSection x = ⊥ :=
  Sieve.ext fun _ _ => Iff.rfl

theorem sieveOfSection_inf :
    (A ⊓ B).sieveOfSection x = A.sieveOfSection x ⊓ B.sieveOfSection x :=
  rfl

theorem sieveOfSection_sup :
    (A ⊔ B).sieveOfSection x = A.sieveOfSection x ⊔ B.sieveOfSection x :=
  rfl

/-- Forcing an implication at `x` is the implication of the sieves of `x`. -/
theorem sieveOfSection_himp :
    (A ⇨ B).sieveOfSection x = A.sieveOfSection x ⇨ B.sieveOfSection x := by
  refine Sieve.ext fun Y f => ?_
  change (∀ ⦃V⦄ (g : op Y ⟶ V), F.map g (F.map f.op x) ∈ A.obj V →
      F.map g (F.map f.op x) ∈ B.obj V) ↔
    ∀ ⦃Z⦄ (g : Z ⟶ Y), F.map (g ≫ f).op x ∈ A.obj (op Z) → F.map (g ≫ f).op x ∈ B.obj (op Z)
  simp only [op_comp, Functor.map_comp_apply]
  exact ⟨fun h _ g => h g.op, fun h _ g => h g.unop⟩

theorem sieveOfSection_compl : Aᶜ.sieveOfSection x = (A.sieveOfSection x)ᶜ := by
  rw [← himp_bot, ← himp_bot, sieveOfSection_himp, sieveOfSection_bot]

end SieveOfSection

end Subfunctor

end CategoryTheory
