/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/

module

public import Mathlib.Order.Heyting.Basic
public import Mathlib.Data.Set.Insert

/-!
# Intuitionistic propositional logic and its Heyting algebra semantics

Formulas of intuitionistic propositional logic are built from atoms, `⊥`, `⊓`, `⊔` and `⇨`, with
the usual abbreviations `⊤ = ⊥ ⇨ ⊥` and `φᶜ = φ ⇨ ⊥`. The derivability relation `Derives Γ φ` is
natural deduction with a set of hypotheses `Γ`.

A valuation of the atoms in a Heyting algebra `H` extends to all formulas (`IPC.eval`). The
Kripke–Joyal semantics of a topos is of this form: `H` is the Heyting algebra of sieves at one
stage, or the frame of subobjects of an object. Soundness says that a derivable formula is true
under every valuation in every Heyting algebra, so a single Heyting algebra in which a formula
fails is a proof that it cannot be derived (see `LawvereTierney.Independence`).

## Main definitions

* `IPC.Formula`: formulas over a type of atoms.
* `IPC.Derives`: natural deduction.
* `IPC.eval`: the value of a formula under a valuation in a Heyting algebra.

## Main results

* `IPC.Derives.sound`: if `Γ` derives `φ`, every element below all the hypotheses is below `φ`.
* `IPC.Derives.eval_eq_top`: a formula derivable from no hypotheses has value `⊤`.
* `IPC.derives_compl_compl_lem`: `¬¬(φ ∨ ¬φ)` is derivable.
-/

@[expose] public section

universe u v

namespace IPC

/-- Formulas of intuitionistic propositional logic. -/
inductive Formula (α : Type u) : Type u
  /-- A propositional variable. -/
  | atom : α → Formula α
  /-- Falsity. -/
  | bot : Formula α
  /-- Conjunction. -/
  | and : Formula α → Formula α → Formula α
  /-- Disjunction. -/
  | or : Formula α → Formula α → Formula α
  /-- Implication. -/
  | imp : Formula α → Formula α → Formula α

namespace Formula

variable {α : Type u}

instance : Bot (Formula α) := ⟨bot⟩
instance : Min (Formula α) := ⟨and⟩
instance : Max (Formula α) := ⟨or⟩
instance : HImp (Formula α) := ⟨imp⟩
instance : Top (Formula α) := ⟨imp bot bot⟩
instance : Compl (Formula α) := ⟨fun φ => imp φ bot⟩

end Formula

variable {α : Type u}

/-- Natural deduction: `Derives Γ φ` means that `φ` follows from the hypotheses in `Γ`. -/
inductive Derives : Set (Formula α) → Formula α → Prop
  /-- Use a hypothesis. -/
  | ax {Γ : Set (Formula α)} {φ : Formula α} : φ ∈ Γ → Derives Γ φ
  /-- Introduction of `⊓`. -/
  | andI {Γ : Set (Formula α)} {φ ψ : Formula α} :
      Derives Γ φ → Derives Γ ψ → Derives Γ (φ ⊓ ψ)
  /-- Left elimination of `⊓`. -/
  | andEl {Γ : Set (Formula α)} {φ ψ : Formula α} : Derives Γ (φ ⊓ ψ) → Derives Γ φ
  /-- Right elimination of `⊓`. -/
  | andEr {Γ : Set (Formula α)} {φ ψ : Formula α} : Derives Γ (φ ⊓ ψ) → Derives Γ ψ
  /-- Left introduction of `⊔`. -/
  | orIl {Γ : Set (Formula α)} {φ ψ : Formula α} : Derives Γ φ → Derives Γ (φ ⊔ ψ)
  /-- Right introduction of `⊔`. -/
  | orIr {Γ : Set (Formula α)} {φ ψ : Formula α} : Derives Γ ψ → Derives Γ (φ ⊔ ψ)
  /-- Elimination of `⊔`, by cases. -/
  | orE {Γ : Set (Formula α)} {φ ψ χ : Formula α} :
      Derives Γ (φ ⊔ ψ) → Derives (insert φ Γ) χ → Derives (insert ψ Γ) χ → Derives Γ χ
  /-- Introduction of `⇨`: discharge a hypothesis. -/
  | impI {Γ : Set (Formula α)} {φ ψ : Formula α} :
      Derives (insert φ Γ) ψ → Derives Γ (φ ⇨ ψ)
  /-- Elimination of `⇨`, modus ponens. -/
  | impE {Γ : Set (Formula α)} {φ ψ : Formula α} :
      Derives Γ (φ ⇨ ψ) → Derives Γ φ → Derives Γ ψ
  /-- From falsity anything follows. -/
  | botE {Γ : Set (Formula α)} {φ : Formula α} : Derives Γ ⊥ → Derives Γ φ

section Semantics

variable {H : Type v} [HeytingAlgebra H]

/-- The value of a formula under a valuation of the atoms in a Heyting algebra. -/
def eval (v : α → H) : Formula α → H
  | .atom a => v a
  | .bot => ⊥
  | .and φ ψ => eval v φ ⊓ eval v ψ
  | .or φ ψ => eval v φ ⊔ eval v ψ
  | .imp φ ψ => eval v φ ⇨ eval v ψ

variable (v : α → H)

@[simp] theorem eval_atom (a : α) : eval v (Formula.atom a) = v a := rfl
@[simp] theorem eval_bot : eval v (⊥ : Formula α) = ⊥ := rfl
@[simp] theorem eval_inf (φ ψ : Formula α) : eval v (φ ⊓ ψ) = eval v φ ⊓ eval v ψ := rfl
@[simp] theorem eval_sup (φ ψ : Formula α) : eval v (φ ⊔ ψ) = eval v φ ⊔ eval v ψ := rfl
@[simp] theorem eval_himp (φ ψ : Formula α) : eval v (φ ⇨ ψ) = eval v φ ⇨ eval v ψ := rfl

@[simp] theorem eval_top : eval v (⊤ : Formula α) = ⊤ := himp_self

@[simp] theorem eval_compl (φ : Formula α) : eval v φᶜ = (eval v φ)ᶜ := himp_bot _

/-- Soundness. If `h` lies below the value of every hypothesis then it lies below the value of
every consequence. Taking `H` to be the sieves at an object, or the subobjects of a presheaf, this
is the soundness of the Kripke–Joyal clauses. -/
theorem Derives.sound {Γ : Set (Formula α)} {φ : Formula α} (d : Derives Γ φ) :
    ∀ h : H, (∀ γ ∈ Γ, h ≤ eval v γ) → h ≤ eval v φ := by
  induction d with
  | ax hφ => exact fun h hh => hh _ hφ
  | andI _ _ ih₁ ih₂ => exact fun h hh => le_inf (ih₁ h hh) (ih₂ h hh)
  | andEl _ ih => exact fun h hh => (ih h hh).trans inf_le_left
  | andEr _ ih => exact fun h hh => (ih h hh).trans inf_le_right
  | orIl _ ih => exact fun h hh => (ih h hh).trans le_sup_left
  | orIr _ ih => exact fun h hh => (ih h hh).trans le_sup_right
  | @orE Γ φ ψ χ _ _ _ ih ih₁ ih₂ =>
    intro h hh
    have hφ : h ⊓ eval v φ ≤ eval v χ := by
      refine ih₁ _ ?_
      rintro γ (rfl | hγ)
      · exact inf_le_right
      · exact inf_le_left.trans (hh γ hγ)
    have hψ : h ⊓ eval v ψ ≤ eval v χ := by
      refine ih₂ _ ?_
      rintro γ (rfl | hγ)
      · exact inf_le_right
      · exact inf_le_left.trans (hh γ hγ)
    calc h = h ⊓ (eval v φ ⊔ eval v ψ) := (inf_eq_left.2 (ih h hh)).symm
      _ = h ⊓ eval v φ ⊔ h ⊓ eval v ψ := inf_sup_left _ _ _
      _ ≤ eval v χ := sup_le hφ hψ
  | @impI Γ φ ψ _ ih =>
    intro h hh
    refine le_himp_iff.2 (ih _ ?_)
    rintro γ (rfl | hγ)
    · exact inf_le_right
    · exact inf_le_left.trans (hh γ hγ)
  | impE _ _ ih₁ ih₂ =>
    exact fun h hh => (le_inf (ih₁ h hh) (ih₂ h hh)).trans himp_inf_le
  | botE _ ih => exact fun h hh => (ih h hh).trans bot_le

/-- A formula derivable without hypotheses has value `⊤` under every valuation. -/
theorem Derives.eval_eq_top {φ : Formula α} (d : Derives ∅ φ) : eval v φ = ⊤ :=
  top_le_iff.1 (d.sound v ⊤ fun _ hγ => hγ.elim)

end Semantics

/-- Falsity is not derivable, since it fails in `Prop`. -/
theorem not_derives_bot : ¬ Derives (∅ : Set (Formula α)) ⊥ := fun d => by
  have := d.eval_eq_top (H := Prop) fun _ => True
  simp at this

/-- The double negation of excluded middle is derivable, although excluded middle itself is not
(see `LawvereTierney.Independence`). -/
theorem derives_compl_compl_lem (φ : Formula α) : Derives ∅ ((φ ⊔ φᶜ)ᶜᶜ) := by
  refine Derives.impI ?_
  have hn : (φ ⊔ φᶜ)ᶜ ∈ insert (φ ⊔ φᶜ)ᶜ (∅ : Set (Formula α)) := Set.mem_insert _ _
  refine Derives.impE (Derives.ax hn) (Derives.orIr (Derives.impI ?_))
  exact Derives.impE (Derives.ax (Set.mem_insert_of_mem _ hn))
    (Derives.orIl (Derives.ax (Set.mem_insert _ _)))

end IPC
