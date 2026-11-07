/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/
import LawvereTierney.Closure
import LawvereTierney.Poset
import Mathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.Topology.Sets.Opens

/-!
# Subtoposes of a presheaf topos on a preorder, and the Alexandrov space

For a preorder `P`, the lower sets of `P` are the subobjects of the terminal presheaf on `P`, and
also the open sets of the Alexandrov topology on `P` in which the open sets are the lower sets.
The nucleus that a Grothendieck topology induces on lower sets (`GrothendieckTopology.toNucleus`)
is the action of the corresponding Lawvere–Tierney topology on subobjects of `1`. Combined with
the equivalence of `LawvereTierney.Poset`, this identifies Grothendieck topologies on `P` with
nuclei on `Opens P`, that is with sublocales of the Alexandrov space.

## Main definitions

* `CategoryTheory.lowerSetOrderIsoSubterminal`: lower sets are subobjects of the terminal
  presheaf.
* `CategoryTheory.lowerSetOrderIsoOpens`: lower sets are the open sets of the Alexandrov topology.
* `Nucleus.transport`: the transport of a nucleus along an order isomorphism.
* `CategoryTheory.GrothendieckTopology.orderIsoNucleusOpens`: Grothendieck topologies on `P` are
  nuclei on `Opens P`.

## Main results

* `CategoryTheory.LawvereTierneyTopology.closure_lowerSetOrderIsoSubterminal`: closure of a
  subobject of `1` for the Lawvere–Tierney topology of `J` is the nucleus of `J` on lower sets.
-/

universe u

namespace Nucleus

variable {X Y : Type*} [SemilatticeInf X] [SemilatticeInf Y]

/-- Transport of a nucleus along an order isomorphism. -/
def transport (e : X ≃o Y) (n : Nucleus X) : Nucleus Y where
  toFun y := e (n (e.symm y))
  map_inf' a b := by rw [e.symm.map_inf, n.map_inf, e.map_inf]
  idempotent' y := by simp
  le_apply' y := by simpa using e.monotone (n.le_apply (x := e.symm y))

@[simp]
theorem transport_apply (e : X ≃o Y) (n : Nucleus X) (y : Y) :
    n.transport e y = e (n (e.symm y)) :=
  rfl

/-- Nuclei on isomorphic semilattices correspond. -/
def orderIsoOfOrderIso (e : X ≃o Y) : Nucleus X ≃o Nucleus Y where
  toFun := transport e
  invFun := transport e.symm
  left_inv n := DFunLike.ext _ _ fun x => by simp
  right_inv n := DFunLike.ext _ _ fun y => by simp
  map_rel_iff' := by
    refine ⟨fun h x => ?_, fun h y => ?_⟩
    · simpa using e.le_iff_le.1 (h (e x))
    · exact e.monotone (h (e.symm y))

end Nucleus

namespace CategoryTheory

open Opposite

variable (P : Type u) [Preorder P]

/-- The terminal presheaf on `P`. -/
abbrev terminalPresheaf : Pᵒᵖ ⥤ Type u :=
  (Functor.const Pᵒᵖ).obj PUnit

variable {P}

/-- Lower sets of `P` are the subobjects of the terminal presheaf. -/
def lowerSetOrderIsoSubterminal : LowerSet P ≃o Subfunctor (terminalPresheaf P) where
  toFun U :=
    { obj p := {_x | p.unop ∈ U}
      map := fun f _ hx => U.lower (leOfHom f.unop) hx }
  invFun G :=
    { carrier := {p | PUnit.unit ∈ G.obj (op p)}
      lower' := fun _ _ h hp => G.map (homOfLE h).op hp }
  left_inv _ := rfl
  right_inv G := Subfunctor.ext (funext fun p => Set.ext fun x => by cases x; rfl)
  map_rel_iff' := by
    refine ⟨fun h p hp => ?_, fun h _ _ hx => h hx⟩
    exact h (op p) (show (PUnit.unit : PUnit) ∈ _ from hp)

theorem mem_lowerSetOrderIsoSubterminal_iff {U : LowerSet P} {p : Pᵒᵖ} {x : PUnit} :
    x ∈ (lowerSetOrderIsoSubterminal U).obj p ↔ p.unop ∈ U :=
  Iff.rfl

/-- For the Lawvere–Tierney topology of `J`, the closure of a subobject of the terminal presheaf
is given by the nucleus of `J` on lower sets. -/
theorem LawvereTierneyTopology.closure_lowerSetOrderIsoSubterminal (J : GrothendieckTopology P)
    (U : LowerSet P) :
    (LawvereTierneyTopology.ofGrothendieckTopology J).closure (lowerSetOrderIsoSubterminal U) =
      lowerSetOrderIsoSubterminal (J.toNucleus U) := by
  refine Subfunctor.ext (funext fun p => Set.ext fun x => ?_)
  change _ ∈ (LawvereTierneyTopology.ofGrothendieckTopology J).toGrothendieckTopology p.unop ↔ _
  rw [LawvereTierneyTopology.toGrothendieckTopology_ofGrothendieckTopology]
  exact Iff.rfl

variable [TopologicalSpace P] [Topology.IsLowerSet P]

/-- Lower sets are the open sets of the Alexandrov topology in which opens are lower sets. -/
def lowerSetOrderIsoOpens : LowerSet P ≃o TopologicalSpace.Opens P where
  toFun U := ⟨U, Topology.IsLowerSet.isOpen_iff_isLowerSet.2 U.lower⟩
  invFun V := ⟨V, Topology.IsLowerSet.isOpen_iff_isLowerSet.1 V.isOpen⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

namespace GrothendieckTopology

variable (P) in
/-- Grothendieck topologies on a preorder `P` are the nuclei on the frame of open sets of the
Alexandrov space of `P`, that is, its sublocales. -/
def orderIsoNucleusOpens : GrothendieckTopology P ≃o Nucleus (TopologicalSpace.Opens P) :=
  (orderIsoNucleus P).trans (Nucleus.orderIsoOfOrderIso lowerSetOrderIsoOpens)

end GrothendieckTopology

end CategoryTheory
