/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/

module

public import LawvereTierney.Logic
public import Mathlib.Order.Antisymmetrization

/-!
# Completeness of intuitionistic propositional logic

`IPC.Derives.sound` says that a derivable formula holds in every Heyting algebra. Here we prove the
converse: if `Γ` does not derive `φ`, there is a Heyting algebra with a valuation that gives every
hypothesis the value `⊤` and `φ` a smaller value.

The algebra is the Lindenbaum algebra of `Γ`. Its elements are formulas, ordered by `φ ≤ ψ` when
`ψ` follows from `Γ` and `φ`, with formulas that follow from each other identified. The
connectives act on classes. The valuation sending each atom to its own class sends every formula
to its class (`IPC.Lindenbaum.eval_mk`), and a class is `⊤` exactly when the formula is
derivable.

## Main definitions

* `IPC.Lindenbaum`: the Lindenbaum algebra of a set of hypotheses, a Heyting algebra.

## Main results

* `IPC.Derives.mono`, `IPC.Derives.cut`: weakening and cut.
* `IPC.derives_iff_forall_eval_eq_top`: `Γ` derives `φ` exactly when `φ` is `⊤` in every Heyting
  algebra and under every valuation that makes the hypotheses `⊤`.
* `IPC.derives_empty_iff`: a formula is derivable exactly when it holds in every Heyting algebra.
-/

@[expose] public section

universe u

namespace IPC

variable {α : Type u} {Γ Δ : Set (Formula α)} {φ ψ : Formula α}

/-- Adding hypotheses preserves derivability. -/
theorem Derives.mono (h : Γ ⊆ Δ) (d : Derives Γ φ) : Derives Δ φ := by
  induction d generalizing Δ with
  | ax hφ => exact .ax (h hφ)
  | andI _ _ ih₁ ih₂ => exact .andI (ih₁ h) (ih₂ h)
  | andEl _ ih => exact .andEl (ih h)
  | andEr _ ih => exact .andEr (ih h)
  | orIl _ ih => exact .orIl (ih h)
  | orIr _ ih => exact .orIr (ih h)
  | orE _ _ _ ih ih₁ ih₂ =>
    exact .orE (ih h) (ih₁ (Set.insert_subset_insert h)) (ih₂ (Set.insert_subset_insert h))
  | impI _ ih => exact .impI (ih (Set.insert_subset_insert h))
  | impE _ _ ih₁ ih₂ => exact .impE (ih₁ h) (ih₂ h)
  | botE _ ih => exact .botE (ih h)

/-- Cut: a derivable formula can be dropped from the hypotheses. -/
theorem Derives.cut (d : Derives Γ φ) (e : Derives (insert φ Γ) ψ) : Derives Γ ψ :=
  .impE (.impI e) d

/-- Weakening that slips a new hypothesis in below the most recent one. -/
theorem Derives.mono_insert (χ : Formula α) (d : Derives (insert φ Γ) ψ) :
    Derives (insert φ (insert χ Γ)) ψ :=
  d.mono (Set.insert_subset_insert (Set.subset_insert _ _))

/-- The formulas over `α`, ordered by `φ ≤ ψ` when `ψ` follows from `φ` together with the
hypotheses `Γ`. This is a synonym for `Formula α`; the Lindenbaum algebra is its
antisymmetrization. -/
def Entailment (_ : Set (Formula α)) : Type u := Formula α

namespace Entailment

instance : Preorder (Entailment Γ) where
  le φ ψ := Derives (insert φ Γ) ψ
  le_refl _ := .ax (Set.mem_insert _ _)
  le_trans _ _ _ h₁ h₂ := h₁.cut (h₂.mono_insert _)

instance : Max (Entailment Γ) := inferInstanceAs (Max (Formula α))
instance : Min (Entailment Γ) := inferInstanceAs (Min (Formula α))
instance : HImp (Entailment Γ) := inferInstanceAs (HImp (Formula α))
instance : Bot (Entailment Γ) := inferInstanceAs (Bot (Formula α))
instance : Top (Entailment Γ) := inferInstanceAs (Top (Formula α))
instance : Compl (Entailment Γ) := inferInstanceAs (Compl (Formula α))

variable {a b c d : Entailment Γ}

protected theorem le_sup_left : a ≤ a ⊔ b := .orIl (.ax (Set.mem_insert _ _))

protected theorem le_sup_right : b ≤ a ⊔ b := .orIr (.ax (Set.mem_insert _ _))

protected theorem sup_le (h₁ : a ≤ c) (h₂ : b ≤ c) : a ⊔ b ≤ c :=
  .orE (.ax (Set.mem_insert _ _)) (Derives.mono_insert _ h₁) (Derives.mono_insert _ h₂)

protected theorem inf_le_left : a ⊓ b ≤ a := .andEl (.ax (Set.mem_insert _ _))

protected theorem inf_le_right : a ⊓ b ≤ b := .andEr (.ax (Set.mem_insert _ _))

protected theorem le_inf (h₁ : a ≤ b) (h₂ : a ≤ c) : a ≤ b ⊓ c := .andI h₁ h₂

protected theorem le_top : a ≤ ⊤ := .impI (.ax (Set.mem_insert _ _))

protected theorem bot_le : ⊥ ≤ a := .botE (.ax (Set.mem_insert _ _))

protected theorem le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  refine ⟨fun h => ?_, fun h => .impI ?_⟩
  · have h₁ : Derives (insert (a ⊓ b) Γ) a := .andEl (.ax (Set.mem_insert _ _))
    have h₂ : Derives (insert (a ⊓ b) Γ) b := .andEr (.ax (Set.mem_insert _ _))
    exact .impE (h₁.cut (Derives.mono_insert _ h)) h₂
  · have : Derives (insert b (insert a Γ)) (a ⊓ b) :=
      .andI (.ax (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (.ax (Set.mem_insert _ _))
    exact this.cut (Derives.mono_insert _ (Derives.mono_insert _ h))

protected theorem sup_mono (h₁ : a ≤ c) (h₂ : b ≤ d) : a ⊔ b ≤ c ⊔ d :=
  Entailment.sup_le (h₁.trans Entailment.le_sup_left) (h₂.trans Entailment.le_sup_right)

protected theorem inf_mono (h₁ : a ≤ c) (h₂ : b ≤ d) : a ⊓ b ≤ c ⊓ d :=
  Entailment.le_inf (Entailment.inf_le_left.trans h₁) (Entailment.inf_le_right.trans h₂)

protected theorem himp_mono (h₁ : c ≤ a) (h₂ : b ≤ d) : a ⇨ b ≤ c ⇨ d :=
  Entailment.le_himp_iff.2 <| (Entailment.le_inf Entailment.inf_le_left
    (Entailment.inf_le_right.trans h₁)).trans <| (Entailment.le_himp_iff.1 le_rfl).trans h₂

end Entailment

/-- The Lindenbaum algebra of the hypotheses `Γ`: formulas up to provable equivalence from `Γ`. -/
abbrev Lindenbaum (Γ : Set (Formula α)) : Type u :=
  Antisymmetrization (Entailment Γ) (· ≤ ·)

namespace Lindenbaum

variable (Γ)

/-- The class of a formula in the Lindenbaum algebra. -/
def mk (φ : Formula α) : Lindenbaum Γ :=
  toAntisymmetrization _ (φ : Entailment Γ)

theorem mk_le_mk_iff {φ ψ : Formula α} : mk Γ φ ≤ mk Γ ψ ↔ Derives (insert φ Γ) ψ :=
  Iff.rfl

instance : HeytingAlgebra (Lindenbaum Γ) :=
  { (inferInstance : PartialOrder (Lindenbaum Γ)) with
    sup := Quotient.map₂' (· ⊔ ·) fun _ _ h₁ _ _ h₂ =>
      ⟨Entailment.sup_mono h₁.1 h₂.1, Entailment.sup_mono h₁.2 h₂.2⟩
    le_sup_left := fun a b => Quotient.inductionOn₂' a b fun _ _ => Entailment.le_sup_left
    le_sup_right := fun a b => Quotient.inductionOn₂' a b fun _ _ => Entailment.le_sup_right
    sup_le := fun a b c => Quotient.inductionOn₃' a b c fun _ _ _ => Entailment.sup_le
    inf := Quotient.map₂' (· ⊓ ·) fun _ _ h₁ _ _ h₂ =>
      ⟨Entailment.inf_mono h₁.1 h₂.1, Entailment.inf_mono h₁.2 h₂.2⟩
    inf_le_left := fun a b => Quotient.inductionOn₂' a b fun _ _ => Entailment.inf_le_left
    inf_le_right := fun a b => Quotient.inductionOn₂' a b fun _ _ => Entailment.inf_le_right
    le_inf := fun a b c => Quotient.inductionOn₃' a b c fun _ _ _ => Entailment.le_inf
    top := mk Γ ⊤
    le_top := fun a => Quotient.inductionOn' a fun _ => Entailment.le_top
    bot := mk Γ ⊥
    bot_le := fun a => Quotient.inductionOn' a fun _ => Entailment.bot_le
    himp := Quotient.map₂' (· ⇨ ·) fun _ _ h₁ _ _ h₂ =>
      ⟨Entailment.himp_mono h₁.2 h₂.1, Entailment.himp_mono h₁.1 h₂.2⟩
    le_himp_iff := fun a b c => Quotient.inductionOn₃' a b c fun _ _ _ => Entailment.le_himp_iff
    compl := Quotient.map' (·ᶜ) fun _ _ h =>
      ⟨Entailment.himp_mono h.2 le_rfl, Entailment.himp_mono h.1 le_rfl⟩
    himp_bot := fun a => Quotient.inductionOn' a fun _ => rfl }

/-- Evaluating a formula at the valuation `a ↦ [a]` gives its own class. -/
theorem eval_mk (φ : Formula α) : eval (fun a => mk Γ (.atom a)) φ = mk Γ φ := by
  induction φ with
  | atom a => rfl
  | bot => rfl
  | and φ ψ ihφ ihψ => rw [eval, ihφ, ihψ]; rfl
  | or φ ψ ihφ ihψ => rw [eval, ihφ, ihψ]; rfl
  | imp φ ψ ihφ ihψ => rw [eval, ihφ, ihψ]; rfl

/-- A class is `⊤` exactly when its formula is derivable from the hypotheses. -/
theorem mk_eq_top_iff : mk Γ φ = ⊤ ↔ Derives Γ φ := by
  rw [← top_le_iff]
  change Derives (insert ⊤ Γ) φ ↔ _
  exact ⟨fun h => (Derives.impI (.ax (Set.mem_insert _ _))).cut h,
    Derives.mono (Set.subset_insert _ _)⟩

end Lindenbaum

/-- Completeness and soundness for Heyting algebras: `Γ` derives `φ` exactly when `φ` has value
`⊤` under every valuation, in every Heyting algebra, that gives the hypotheses the value `⊤`. -/
theorem derives_iff_forall_eval_eq_top :
    Derives Γ φ ↔ ∀ (H : Type u) [HeytingAlgebra H] (v : α → H),
      (∀ γ ∈ Γ, eval v γ = ⊤) → eval v φ = ⊤ := by
  refine ⟨fun d H _ v hv => top_le_iff.1 (d.sound v ⊤ fun γ hγ => (hv γ hγ).ge), fun h => ?_⟩
  rw [← Lindenbaum.mk_eq_top_iff, ← Lindenbaum.eval_mk Γ]
  exact h _ _ fun γ hγ => by
    rw [Lindenbaum.eval_mk, Lindenbaum.mk_eq_top_iff]
    exact .ax hγ

/-- A formula is derivable exactly when it has value `⊤` in every Heyting algebra under every
valuation. -/
theorem derives_empty_iff :
    Derives (∅ : Set (Formula α)) φ ↔
      ∀ (H : Type u) [HeytingAlgebra H] (v : α → H), eval v φ = ⊤ := by
  simp [derives_iff_forall_eval_eq_top]

end IPC
