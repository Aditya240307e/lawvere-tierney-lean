/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/

module

public import LawvereTierney.DoubleNegation
public import LawvereTierney.Forcing
public import Mathlib.Order.Sublocale

/-!
# Forcing in the sheaf topos

Fix a Lawvere–Tierney topology `L`. A subpresheaf `A ⊆ F` is *closed* if `L.closure A = A`. These
are the propositions of the sheaf semantics. When `F` is a sheaf they are exactly the subpresheaves
that are sheaves (`mem_closedSubobjects_iff_isSheaf`); comparing them with the subobjects of `F` in
the category of sheaves is not carried out here. The closed subpresheaves form a sublocale of the
frame of all subpresheaves, which has two consequences:

* `⊓`, `⇨` and `∀` of closed subpresheaves are computed as for presheaves (`Subfunctor.forall` is
  closed when its argument is, see `forall_mem_closedSubobjects`);
* `⊔`, `⊥` and `∃` have to be closed up. Since `x ∈ (L.closure A).obj U` says that `A` holds at
  `x` on a covering sieve of `U`, this gives the usual clauses of sheaf semantics: a disjunction
  holds when it holds locally, and `⊥` holds exactly on objects covered by the empty sieve.

For the double negation topology every closed subpresheaf has a complement, so the logic of the
corresponding sheaf topos is classical, although that of the presheaf topos is not.

## Main definitions

* `LawvereTierneyTopology.closedSubobjects`: the sublocale of closed subpresheaves.

## Main results

* `LawvereTierneyTopology.mem_closure_iff_exists`: the closure is membership on a covering sieve.
* `LawvereTierneyTopology.mem_closedSubobjects_iff_isSheaf`: inside a sheaf, the closed
  subpresheaves are the ones that are sheaves.
* `LawvereTierneyTopology.coe_sup`, `LawvereTierneyTopology.coe_bot`: joins and `⊥` in the frame of
  closed subpresheaves.
* `LawvereTierneyTopology.mem_closure_sup_iff`, `LawvereTierneyTopology.mem_closure_bot_iff`,
  `LawvereTierneyTopology.mem_closure_image_iff`: the local clauses for `∨`, `⊥` and `∃`.
* `LawvereTierneyTopology.closure_image_le_iff`: `∃` is left adjoint to pullback on closed
  subpresheaves.
* `LawvereTierneyTopology.forall_mem_closedSubobjects`: `∀` preserves closed subpresheaves.
* `LawvereTierneyTopology.closure_sup_compl`, `LawvereTierneyTopology.isCompl_compl_doubleNegation`:
  excluded middle for the double negation topology.

## References

* [S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92], Chapter VI.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite

namespace LawvereTierneyTopology

variable {C : Type u} [Category.{v} C] (L : LawvereTierneyTopology C) {F F' : Cᵒᵖ ⥤ Type w}

/-- A section lies in the closure of `A` when its restrictions lie in `A` along a covering sieve. -/
theorem mem_closure_iff_exists {A : Subfunctor F} {X : Cᵒᵖ} {x : F.obj X} :
    x ∈ (L.closure A).obj X ↔ ∃ S ∈ L.toGrothendieckTopology X.unop,
      ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → F.map f.op x ∈ A.obj (op Y) := by
  refine ⟨fun h => ⟨A.sieveOfSection x, h, fun _ _ hf => hf⟩, ?_⟩
  rintro ⟨S, hS, h⟩
  exact L.toGrothendieckTopology.superset_covering (fun _ f hf => h f hf) hS

variable (F) in
/-- The closed subpresheaves of `F`, as a sublocale of the frame of subpresheaves. -/
def closedSubobjects : Sublocale (Subfunctor F) :=
  (L.closureNucleus F).toSublocale

theorem mem_closedSubobjects_iff {A : Subfunctor F} :
    A ∈ L.closedSubobjects F ↔ L.closure A = A :=
  Nucleus.mem_range

/-- A closed subpresheaf is determined locally: a section belongs to it as soon as its
restrictions do along a covering sieve. -/
theorem mem_iff_exists_of_mem_closedSubobjects {A : Subfunctor F}
    (hA : A ∈ L.closedSubobjects F) {X : Cᵒᵖ} {x : F.obj X} :
    x ∈ A.obj X ↔ ∃ S ∈ L.toGrothendieckTopology X.unop,
      ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → F.map f.op x ∈ A.obj (op Y) := by
  rw [← L.mem_closure_iff_exists, (L.mem_closedSubobjects_iff.1 hA)]

/-- A subpresheaf of a sheaf is closed exactly when it is itself a sheaf. -/
theorem mem_closedSubobjects_iff_isSheaf
    (hF : Presieve.IsSheaf L.toGrothendieckTopology F) {A : Subfunctor F} :
    A ∈ L.closedSubobjects F ↔ Presieve.IsSheaf L.toGrothendieckTopology A.toFunctor :=
  L.mem_closedSubobjects_iff.trans (eq_comm.trans (A.eq_sheafify_iff hF))

/-! ### Disjunction, falsity and the existential quantifier -/

theorem mem_closure_sup_iff {A B : Subfunctor F} {X : Cᵒᵖ} {x : F.obj X} :
    x ∈ (L.closure (A ⊔ B)).obj X ↔ ∃ S ∈ L.toGrothendieckTopology X.unop,
      ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f →
        F.map f.op x ∈ A.obj (op Y) ∨ F.map f.op x ∈ B.obj (op Y) :=
  L.mem_closure_iff_exists

/-- `⊥` holds at a section exactly when the empty sieve covers its stage. -/
theorem mem_closure_bot_iff {X : Cᵒᵖ} {x : F.obj X} :
    x ∈ (L.closure (⊥ : Subfunctor F)).obj X ↔ ⊥ ∈ L.toGrothendieckTopology X.unop := by
  rw [mem_closure_iff_exists]
  refine ⟨fun ⟨S, hS, h⟩ => ?_, fun h => ⟨⊥, h, fun _ _ hf => hf.elim⟩⟩
  have : S = ⊥ := eq_bot_iff.2 fun _ f hf => by simpa using h f hf
  rwa [this] at hS

theorem mem_closure_image_iff {A : Subfunctor F} (p : F ⟶ F') {X : Cᵒᵖ} {x : F'.obj X} :
    x ∈ (L.closure (A.image p)).obj X ↔ ∃ S ∈ L.toGrothendieckTopology X.unop,
      ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f →
        ∃ y ∈ A.obj (op Y), p.app (op Y) y = F'.map f.op x :=
  L.mem_closure_iff_exists

/-- The restriction of `L.closureNucleus` to its range sends `A` to its closure. -/
theorem restrict_closedSubobjects (A : Subfunctor F) :
    (L.closedSubobjects F).restrict A = ⟨L.closure A, A, rfl⟩ :=
  Nucleus.restrict_toSublocale _ _

/-- The join of two closed subpresheaves is the closure of their union. -/
theorem coe_sup (A B : L.closedSubobjects F) :
    ((A ⊔ B : L.closedSubobjects F) : Subfunctor F) = L.closure (A.1 ⊔ B.1) := by
  have h : (L.closedSubobjects F).restrict (A.1 ⊔ B.1) =
      (L.closedSubobjects F).restrict A.1 ⊔ (L.closedSubobjects F).restrict B.1 :=
    map_sup _ _ _
  rw [Sublocale.restrict_of_mem A.2, Sublocale.restrict_of_mem B.2,
    restrict_closedSubobjects] at h
  exact (congrArg Subtype.val h).symm

/-- `⊥` in the frame of closed subpresheaves is the closure of the empty subpresheaf. -/
theorem coe_bot : ((⊥ : L.closedSubobjects F) : Subfunctor F) = L.closure ⊥ := by
  have h : (L.closedSubobjects F).restrict (⊥ : Subfunctor F) = ⊥ := map_bot _
  rw [restrict_closedSubobjects] at h
  exact (congrArg Subtype.val h).symm

/-- On closed subpresheaves, `∃` along `p` is left adjoint to pullback along `p`. -/
theorem closure_image_le_iff {A : Subfunctor F} {B : Subfunctor F'}
    (hB : B ∈ L.closedSubobjects F') (p : F ⟶ F') :
    L.closure (A.image p) ≤ B ↔ A ≤ B.preimage p := by
  rw [← Subfunctor.image_le_iff]
  refine ⟨fun h => L.le_closure.trans h, fun h => ?_⟩
  simpa [L.mem_closedSubobjects_iff.1 hB] using L.closure_mono h

/-! ### The universal quantifier -/

theorem closure_forall_le (A : Subfunctor F) (p : F ⟶ F') :
    L.closure (A.forall p) ≤ (L.closure A).forall p := by
  rw [Subfunctor.le_forall_iff, ← L.closure_preimage]
  exact L.closure_mono (Subfunctor.le_forall_iff.1 le_rfl)

/-- Closed subpresheaves are closed under `∀`, so the clause for `∀` is the presheaf one. -/
theorem forall_mem_closedSubobjects {A : Subfunctor F} (hA : A ∈ L.closedSubobjects F)
    (p : F ⟶ F') : A.forall p ∈ L.closedSubobjects F' := by
  rw [mem_closedSubobjects_iff] at hA ⊢
  have := L.closure_forall_le A p
  rw [hA] at this
  exact le_antisymm this L.le_closure

/-! ### Excluded middle for the double negation topology -/

section DoubleNegation

theorem closure_bot_doubleNegation (F : Cᵒᵖ ⥤ Type w) :
    (doubleNegation C).closure (⊥ : Subfunctor F) = ⊥ := by
  refine Subfunctor.ext (funext fun X => Set.ext fun x => ?_)
  rw [mem_closure_iff, Subfunctor.sieveOfSection_bot, doubleNegation_j, compl_bot, compl_top,
    ← Sieve.id_mem_iff_eq_top]
  exact ⟨fun h => h, fun h => h⟩

theorem closure_sup_compl (A : Subfunctor F) : (doubleNegation C).closure (A ⊔ Aᶜ) = ⊤ := by
  refine eq_top_iff.2 fun X x _ => ?_
  rw [mem_closure_iff, Subfunctor.sieveOfSection_sup, Subfunctor.sieveOfSection_compl]
  exact (compl_compl_eq_top_iff _).2 (sup_compl_mem_dense _)

/-- Negation in the frame of `¬¬`-closed subpresheaves is the presheaf one. -/
theorem coe_compl_doubleNegation (A : (doubleNegation C).closedSubobjects F) :
    ((Aᶜ : (doubleNegation C).closedSubobjects F) : Subfunctor F) = (A : Subfunctor F)ᶜ := by
  change (A : Subfunctor F) ⇨ ((⊥ : (doubleNegation C).closedSubobjects F) : Subfunctor F) = _
  rw [coe_bot, closure_bot_doubleNegation, himp_bot]

/-- The sheaf semantics for the double negation topology is classical: every closed subpresheaf
has a complement. -/
theorem isCompl_compl_doubleNegation (A : (doubleNegation C).closedSubobjects F) :
    IsCompl A Aᶜ := by
  refine ⟨disjoint_compl_right, codisjoint_iff.2 (Subtype.ext ?_)⟩
  rw [coe_sup, coe_compl_doubleNegation, closure_sup_compl]
  rfl

end DoubleNegation

end LawvereTierneyTopology

end CategoryTheory
