# Lawvere–Tierney topologies in Lean 4

A Lean 4 formalisation, on top of Mathlib, of Lawvere–Tierney topologies on presheaf toposes: how
they correspond to Grothendieck topologies on the underlying category, what they do to the internal
logic (Kripke–Joyal forcing, Heyting algebras of subobjects, intuitionistic propositional logic),
and what everything looks like when the category is a poset, where topologies become nuclei on the
frame of lower sets and the Alexandrov topology enters.

Author: Aditya Ekbote

Everything is proved. There is no `sorry`, and `#print axioms` on the statements listed below shows
only `propext`, `Classical.choice` and `Quot.sound`.

## Overview

A Lawvere–Tierney topology on the presheaf category `Cᵒᵖ ⥤ Type _` is a morphism `j : Ω ⟶ Ω` of the
subobject classifier, with `true ≫ j = true`, `j ≫ j = j` and `∧ ≫ j = (j × j) ≫ ∧`. Since `Ω X` is
the set of sieves on `X`, this is a family of maps `j X : Sieve X → Sieve X` that commute with
pullback, and the three equations read `j ⊤ = ⊤`, `j (j S) = j S` and `j (S ⊓ T) = j S ⊓ j T`.
`Basic` works with this form, and `Textbook` shows that it agrees with the one stated with `Ω`,
`true` and the internal `∧`.

| Layer | Modules | What is proved |
| --- | --- | --- |
| Topologies | `Basic`, `Textbook` | Lawvere–Tierney topologies on `Cᵒᵖ ⥤ Type _` and Grothendieck topologies on `C` are isomorphic as ordered sets. The sieve-wise definition is equivalent to the one using `Ω`, `true` and the internal `∧`. |
| Closure and sheaves | `Closure`, `Sheaf` | `j` acts on subpresheaves, with `χ (closure A) = χ A ≫ j`. Dense subpresheaves are the locally surjective ones. A presheaf is a sheaf iff it has unique extensions along dense subpresheaves. The sieves fixed by `j` form the classifier of the sheaf category. |
| Forcing | `Heyting`, `Forcing`, `SheafForcing` | Sieves and subpresheaves are Heyting algebras whose operations are the Kripke–Joyal clauses. For a topology `j`, the closed subpresheaves form a sublocale (inside a sheaf, they are the subpresheaves that are sheaves), and `∨`, `⊥`, `∃` hold exactly when they hold on a covering sieve. |
| Classical logic | `DoubleNegation`, `Examples` | `j S = Sᶜᶜ` is a Lawvere–Tierney topology whose Grothendieck topology is the dense topology. For it every closed subpresheaf has a complement, although excluded middle fails in the presheaf topos of the chain `0 ≤ 1`. |
| Propositional logic | `Logic`, `Independence`, `Completeness` | Intuitionistic natural deduction is sound and complete for Heyting algebras: a formula is derivable iff it is `⊤` under every valuation in every Heyting algebra, completeness coming from the Lindenbaum algebra. Hence `p ∨ ¬p` and `¬¬p ⇨ p` are not derivable, while `¬¬(p ∨ ¬p)` is. In the `¬¬`-closed subpresheaves, `φ ∨ ¬φ` is true for every valuation. |
| Posets | `Poset`, `SubsetTopology` | For a preorder `P`, Grothendieck topologies on `P` are nuclei on `LowerSet P`. A poset is well-founded iff every topology on it comes from a subset. In that case topologies are the same as subsets of `P` (order reversed), so a finite poset with `n` elements has `2 ^ n` of them. Otherwise some topology comes from no subset. |
| Alexandrov spaces | `Alexandrov` | Lower sets are the subobjects of the terminal presheaf and the open sets of the Alexandrov topology. On them the Lawvere–Tierney topology of `J` acts as the nucleus of `J`, so topologies on `P` are nuclei on `Opens P`. |

## Headline statements

Signatures are abbreviated: universe levels and instance arguments are left out, and everything
except `IPC` lives in the namespace `CategoryTheory`.

```lean
-- Basic
structure LawvereTierneyTopology (C : Type u) [Category.{v} C] where
  j : ∀ X : C, Sieve X → Sieve X
  natural : ∀ {X Y : C} (f : Y ⟶ X) (S : Sieve X), (j X S).pullback f = j Y (S.pullback f)
  top : ∀ X : C, j X ⊤ = ⊤
  idem : ∀ (X : C) (S : Sieve X), j X (j X S) = j X S
  inf : ∀ (X : C) (S T : Sieve X), j X (S ⊓ T) = j X S ⊓ j X T

def LawvereTierneyTopology.orderIsoGrothendieckTopology (C : Type u) [Category.{v} C] :
    GrothendieckTopology C ≃o LawvereTierneyTopology C

-- Textbook: `TextbookTopology C` bundles `j : Ω ⟶ Ω` with `truth ≫ j = truth`, `j ≫ j = j`
-- and `(j ⊗ₘ j) ≫ sieveInf = sieveInf ≫ j`
def LawvereTierneyTopology.equivTextbookTopology (C : Type u) [Category.{v} C] :
    LawvereTierneyTopology C ≃ TextbookTopology C

-- Closure and Sheaf
theorem LawvereTierneyTopology.χ_closure (L : LawvereTierneyTopology C) (A : Subfunctor F) :
    Presheaf.χ (L.closure A).ι = Presheaf.χ A.ι ≫ L.hom

theorem LawvereTierneyTopology.isSheaf_iff_existsUnique_extension
    (L : LawvereTierneyTopology C) (P : Cᵒᵖ ⥤ Type u) :
    Presieve.IsSheaf L.toGrothendieckTopology P ↔
      ∀ (F : Cᵒᵖ ⥤ Type u) (A : Subfunctor F), L.IsDense A →
        ∀ φ : A.toFunctor ⟶ P, ∃! ψ : F ⟶ P, A.ι ≫ ψ = φ

-- Forcing and SheafForcing
theorem Subfunctor.sieveOfSection_himp (A B : Subfunctor F) (x : F.obj X) :
    (A ⇨ B).sieveOfSection x = A.sieveOfSection x ⇨ B.sieveOfSection x

theorem LawvereTierneyTopology.doubleNegation_toGrothendieckTopology :
    (doubleNegation C).toGrothendieckTopology = GrothendieckTopology.dense

theorem LawvereTierneyTopology.isCompl_compl_doubleNegation
    (A : (doubleNegation C).closedSubobjects F) : IsCompl A Aᶜ

-- Logic, Independence and Completeness
theorem IPC.Derives.sound (d : Derives Γ φ) :
    ∀ h : H, (∀ γ ∈ Γ, h ≤ eval v γ) → h ≤ eval v φ

theorem IPC.not_derives_lem : ¬ Derives ∅ lem

theorem IPC.derives_iff_forall_eval_eq_top :
    Derives Γ φ ↔ ∀ (H : Type u) [HeytingAlgebra H] (v : α → H),
      (∀ γ ∈ Γ, eval v γ = ⊤) → eval v φ = ⊤

-- Poset, SubsetTopology and Alexandrov
def GrothendieckTopology.orderIsoNucleus (P : Type u) [Preorder P] :
    GrothendieckTopology P ≃o Nucleus (LowerSet P)

def GrothendieckTopology.orderIsoSubset (P : Type u) [PartialOrder P] [WellFoundedLT P] :
    (Set P)ᵒᵈ ≃o GrothendieckTopology P

theorem GrothendieckTopology.wellFoundedLT_iff_forall_eq_ofSubset [PartialOrder P] :
    WellFoundedLT P ↔ ∀ J : GrothendieckTopology P, ∃ X, J = ofSubset X

theorem GrothendieckTopology.card_eq_two_pow [PartialOrder P] [Fintype P]
    [Fintype (GrothendieckTopology P)] :
    Fintype.card (GrothendieckTopology P) = 2 ^ Fintype.card P

def GrothendieckTopology.orderIsoNucleusOpens (P : Type u) [Preorder P] [TopologicalSpace P]
    [Topology.IsLowerSet P] : GrothendieckTopology P ≃o Nucleus (TopologicalSpace.Opens P)
```

## Mathematical notes

### Topologies

Naturality of `j` together with `j ⊤ = ⊤` gives `S ≤ j S`: an arrow `f` lies in `S` exactly when
`f* S = ⊤`, and then `f* (j S) = j (f* S) = j ⊤ = ⊤` (`le_j`). With idempotence and
meet-preservation this makes each `j X` a nucleus on the frame of sieves on `X` (`nucleus`). A sieve
covers when `j` sends it to `⊤`, and this family is a Grothendieck topology
(`toGrothendieckTopology`, via Mathlib's `topologyOfClosureOperator`). Conversely a Grothendieck
topology `J` gives `j S = J.close S` (`ofGrothendieckTopology`). The two constructions are inverse
and preserve the order (`orderIsoGrothendieckTopology`). Meet-preservation is not really needed as
an axiom: `ofMonotone` builds a topology from a natural, idempotent, monotone `j` with `j ⊤ = ⊤`.

In `Textbook`, `Ω` is `Functor.sieves C` and `true` is Mathlib's `Presheaf.truth`. The internal `∧`
(`Presheaf.sieveInf`) is shown to be the characteristic map of `⟨true, true⟩ : 1 ⟶ Ω ⊗ Ω`, which is
how `∧` is defined in a general topos (`sieveInf_eq_χ`). The three equations on `j : Ω ⟶ Ω` then
say the same thing as the three sieve-wise equations (`equivTextbookTopology`).

### Closure, density and sheaves

For `A ⊆ F`, the closure consists of the sections of `F` that lie in `A` on a covering sieve. This
is Mathlib's `Subfunctor.sheafify` for the topology of `j`, and the sieve of a section of the
closure is `j` applied to its sieve in `A` (`sieveOfSection_closure`). Equivalently
`χ (closure A) = χ A ≫ j` (`χ_closure`). Closure is a nucleus on subpresheaves and commutes with
pullback (`closureNucleus`, `closure_preimage`). A subpresheaf is dense when its closure is
everything, which happens exactly when its inclusion is locally surjective
(`isDense_iff_isLocallySurjective`). Sheaves are the presheaves with unique extensions along dense
subpresheaves (`isSheaf_iff_existsUnique_extension`), which is how sheaves are defined from `j` in
the topos-theoretic literature. The sieves fixed by `j` are the presheaf underlying Mathlib's
`Sheaf.Ω`, the classifier of the sheaf category (`Ω_obj_eq_fixedSieves`).

### Forcing

For a presheaf `F`, a subpresheaf `A ⊆ F` is a proposition about a variable ranging over `F`, and
`x ∈ A(U)` reads "`U` forces `A(x)`". The subpresheaves form a frame in which `⊓` and `⊤` are
computed stage by stage, and for `x ∈ F(U)`

* `x ∈ (A ⇨ B)(U)` iff for every arrow `f : V ⟶ U`, `f*x ∈ A(V)` implies `f*x ∈ B(V)`;
* `x ∈ Aᶜ(U)` iff for every arrow `f : V ⟶ U`, `f*x ∉ A(V)`.

These are the Kripke–Joyal clauses (`Subfunctor.mem_himp_iff`, `Subfunctor.mem_compl_iff`). For a
map `p : F ⟶ G`, `∃` along `p` is the image and `∀` along `p` is the right adjoint of pullback
(`Subfunctor.forall`, `Subfunctor.le_forall_iff`). Sending a section to the sieve of arrows along
which it lies in `A` turns each connective into the same operation on sieves, which is why the logic
at each stage is that of the Heyting algebra of sieves (`Subfunctor.sieveOfSection_himp` and the
lemmas around it).

For a Lawvere–Tierney topology `j`, the propositions of the sheaf semantics are the closed
subpresheaves, those with `closure A = A`. They form a sublocale of the frame of subpresheaves
(`closedSubobjects`), and inside a sheaf they are exactly the subpresheaves that are themselves
sheaves (`mem_closedSubobjects_iff_isSheaf`, from Mathlib's `Subfunctor.eq_sheafify_iff`). Joins and
`⊥` are the closures of the presheaf ones (`coe_sup`, `coe_bot`), `∃` is left adjoint to pullback on
closed subpresheaves (`closure_image_le_iff`), and `∀` preserves closedness
(`forall_mem_closedSubobjects`). Because `x ∈ closure A` says that `x` lies in `A` on a covering
sieve, the closed-up clauses unwind to the usual local ones: a disjunction holds when it holds on a
covering sieve, `⊥` holds exactly where the empty sieve covers, and an existential holds when
witnesses exist on a covering sieve (`mem_closure_sup_iff`, `mem_closure_bot_iff`,
`mem_closure_image_iff`).

### Double negation, and the failure of excluded middle

The double negation topology has `j S = Sᶜᶜ`, and `Sᶜᶜ = ⊤` is exactly the covering condition of
Mathlib's dense topology (`doubleNegation_toGrothendieckTopology`). For this topology the closure of
`⊥` is `⊥`, so negation of closed subpresheaves is the presheaf negation
(`coe_compl_doubleNegation`), and `closure (A ⊔ Aᶜ) = ⊤` because `S ⊔ Sᶜ` always covers
(`sup_compl_mem_dense`, `closure_sup_compl`). Every closed subpresheaf therefore has a complement
(`isCompl_compl_doubleNegation`), so the sheaf semantics is classical.

In the presheaf topos itself, excluded middle already fails for the chain `0 ≤ 1` (the Sierpiński
topos). The sieve `S` on `1` of the arrows out of `0` has empty complement, so `S ⊔ Sᶜ ≠ ⊤`
(`Examples.sup_compl_ne_top`), whereas this same `S` covers `1` for the dense topology
(`Examples.twoChainSieve_mem_dense`).

### Propositional logic

`IPC.Formula` has atoms, `⊥`, `⊓`, `⊔` and `⇨`, with `⊤` and `ᶜ` as abbreviations. `IPC.Derives Γ φ`
is natural deduction, and `IPC.eval` interprets a formula in any Heyting algebra, for instance the
sieves on an object or the closed subpresheaves of a presheaf. Soundness (`Derives.sound`) is stated
as: if `h` lies below every hypothesis, then it lies below the conclusion. This avoids infinite
meets. Interpreting `p` as `Examples.twoChainSieve` in the sieves on `1` for the chain `0 ≤ 1` shows
that neither `p ∨ ¬p` nor `¬¬p ⇨ p` is derivable (`not_derives_lem`,
`not_derives_doubleNegation_elim`). The formula `¬¬(p ∨ ¬p)` is derivable
(`derives_compl_compl_lem`), and on sieves it is the statement `sup_compl_mem_dense`. In the
`¬¬`-closed subpresheaves, `φ ∨ ¬φ` has value `⊤` under every valuation (`eval_lem_doubleNegation`).

Conversely, if `Γ` does not derive `φ`, some Heyting algebra separates them. Order the formulas by
`φ ≤ ψ` when `Derives (insert φ Γ) ψ`, which needs weakening and cut (`Derives.mono`,
`Derives.cut`), and identify formulas that are below each other. This is Mathlib's
`Antisymmetrization` of the preorder `Entailment Γ`, called `Lindenbaum Γ`. Each connective is a
lattice operation of the quotient because the natural deduction rules give the universal
properties of `⊔`, `⊓`, `⊤`, `⊥` and `⇨` (`Entailment.le_himp_iff` is the deduction theorem), and a
connective is well defined on classes because it is monotone in the right sense. The valuation
`a ↦ [a]` evaluates every formula to its own class (`Lindenbaum.eval_mk`) and a class is `⊤`
exactly when its formula is derivable (`Lindenbaum.mk_eq_top_iff`). Together with soundness this
is `derives_iff_forall_eval_eq_top`, and for no hypotheses `derives_empty_iff`: a formula is
derivable iff it is `⊤` in every Heyting algebra. This is completeness for the algebraic
semantics. Completeness for Kripke models, that is for lower sets of posets, is a stronger
statement and is not formalised.

### Posets

For a preorder `P`, a sieve on `p` is a lower set contained in `Iic p`, so a lower set `U` gives a
sieve `U ∩ Iic p` at each `p`. A Grothendieck topology `J` induces the map
`U ↦ {p | U ∩ Iic p ∈ J p}` on `LowerSet P`. It preserves meets because `J` is closed under
intersection, it is idempotent by transitivity, and it is inflationary because the maximal sieve
covers (`toNucleus`). Conversely a nucleus `n` gives the topology in which a sieve `S` on `p` covers
when `p ∈ n S`, taking `S` as a lower set (`ofNucleus`). The two are inverse because sieves are
lower sets (`orderIsoNucleus`).

For a subset `X ⊆ P`, the sieves on `p` containing every element of `X` below `p` form a topology
`ofSubset X`. If `P` is well-founded then every topology is of this form, for the unique `X` of
points `p` whose sieve of strict predecessors is not covering (`eq_ofSubset_uncovered`,
`uncovered_ofSubset`). One inclusion: if a covering sieve of `p` missed some `q ≤ p` in `X`, its
pullback to `q` would lie inside the strict predecessors of `q`, which would then cover, contrary to
`q ∈ X`. The other is well-founded induction on `p` using transitivity. Counting subsets gives
`2 ^ n` topologies on an `n`-element poset (`card_eq_two_pow`). The well-founded case is Theorem
2.12 of Lindenhovius (for Artinian posets), and the comparison with nuclei is in his Appendix B.

The converse of that theorem is formalised too. Suppose `X` is nonempty and every point of `X` has a
smaller point in `X`, as happens in any poset that is not well-founded. Let `meeting X` consist of
the sieves `S` on `p` such that for every `q ≤ p` above a point of `X`, `S` contains a point of `X`
below `q`. This is a topology (`meeting`). Since points of `X` have smaller points in `X`, the
strict predecessors of every `p` cover (`strict_mem_meeting`). If `meeting X` were `ofSubset Y`
then no `p` could lie in `Y`, because the strict predecessors of `p` cover for `ofSubset Y` only
when `p ∉ Y`, so `Y = ∅`. But `ofSubset ∅` makes the empty sieve cover every point, whereas for
`meeting X` the empty sieve does not cover a point of `X` (`meeting_ne_ofSubset`). Hence a poset is
well-founded exactly when all its topologies are subset topologies
(`wellFoundedLT_iff_forall_eq_ofSubset`). For the integers, `X = ℤ` works
(`exists_forall_ne_ofSubset_int`).

### Alexandrov spaces

The lower sets of `P` are the subobjects of the terminal presheaf (`lowerSetOrderIsoSubterminal`),
and also the open sets of the Alexandrov topology in which opens are lower sets
(`lowerSetOrderIsoOpens`). The closure of the subobject of `1` given by `U`, for the Lawvere–Tierney
topology of `J`, is the subobject given by `J.toNucleus U`
(`closure_lowerSetOrderIsoSubterminal`). Transporting along `LowerSet P ≃o Opens P` gives
`GrothendieckTopology P ≃o Nucleus (Opens P)` (`orderIsoNucleusOpens`): a topology on `P` is a
nucleus on the frame of opens of the Alexandrov space.

## Relation to Mathlib

Mathlib provides Grothendieck topologies, the closure of a sieve and `topologyOfClosureOperator`
(`Sites/Closed`), `Subfunctor.sheafify`, the dense topology, the classifier of a presheaf category
and of a sheaf category (`Topos/Sheaf`), nuclei and sublocales. The implementation note in
`Sites/Grothendieck.lean` says that the definition of a Grothendieck topology was chosen so that it
matches Lawvere–Tierney topologies, but at the Mathlib commit used here there is no definition of a
Lawvere–Tierney topology. This repository adds that definition, the correspondence with Grothendieck
topologies and its textbook form, the statements about closure, density and sheaves, the forcing and
logic layers, and the results on posets and Alexandrov spaces. The Mathlib material above is used
directly and not reproved. Mathlib has no Lindenbaum algebra, so the one in `Completeness` is built
from `Antisymmetrization`.

## What is not formalised

* Closed subpresheaves of a sheaf are shown to be its subpresheaves that are sheaves, but they are
  not compared with the subobjects of the sheaf in the category of sheaves. So `SheafForcing` is not
  tied to the internal logic of that category. That the sheaf category is a topos is in Mathlib and
  is not repeated here.
* The logic is propositional. Quantifiers appear as adjoints on subpresheaves, but there is no deep
  embedding of first-order logic or dependent type theory. Completeness is proved for Heyting
  algebras, not for Kripke models: representing a Heyting algebra as lower sets of a poset by prime
  filters, which would show that presheaf toposes on posets already detect every non-theorem, is
  not done.
* For posets, the statements listed above are all that is proved. In particular the following are
  not formalised: that subtoposes of the presheaf topos on `P` correspond to topologies, and that
  sheaves on the Alexandrov space are presheaves on `P` (the comparison lemma).

## Building

The project is pinned to Lean `v4.36.0-rc2` and to the Mathlib commit recorded in `lakefile.toml`
and `lake-manifest.json`. With `elan` installed:

```
lake exe cache get
lake build
```

`lake exe cache get` downloads the compiled Mathlib files when they exist for the pinned commit.
Without them the first build compiles Mathlib from source. All files use Lean's module system, as
Mathlib does. A complete build produces no warnings.

## Layout

```
LawvereTierney.lean            imports everything
LawvereTierney/
  Basic.lean                   the definition, and the match with Grothendieck topologies
  Heyting.lean                 the frame of sieves
  Textbook.lean                the definition stated with Ω, true and the internal ∧
  Forcing.lean                 Kripke–Joyal clauses on subpresheaves
  Closure.lean                 closure and density of subpresheaves
  Sheaf.lean                   sheaves as objects with unique extensions along dense subpresheaves
  DoubleNegation.lean          the topology j S = Sᶜᶜ
  Examples.lean                excluded middle fails for the chain 0 ≤ 1
  SheafForcing.lean            closed subpresheaves, and forcing in the sheaf semantics
  Logic.lean                   intuitionistic propositional calculus and its semantics
  Independence.lean            what is not derivable, and what is valid in ¬¬-sheaves
  Completeness.lean            derivable means true in every Heyting algebra (Lindenbaum algebra)
  Poset.lean                   topologies on a preorder are nuclei on its lower sets
  SubsetTopology.lean          topologies are subsets exactly when the poset is well-founded
  Alexandrov.lean              the same, on the opens of the Alexandrov space
docs/references.bib            the bibliography cited in the docstrings
```

## References

* S. Mac Lane and I. Moerdijk, *Sheaves in Geometry and Logic*, Springer, 1992. Chapter I
  (presheaves and their classifier), Chapter III (Grothendieck topologies), Chapter V (local
  operators, that is Lawvere–Tierney topologies) and Chapter VI (Kripke–Joyal semantics).
* P. T. Johnstone, *Sketches of an Elephant: A Topos Theory Compendium*, vol. 1, Oxford University
  Press, 2002. Section A4.4.
* A. J. Lindenhovius, *Grothendieck topologies on posets*,
  [arXiv:1405.4408](https://arxiv.org/abs/1405.4408).
* J. Hemelaer, *Grothendieck topologies on posets*,
  [arXiv:1811.10039](https://arxiv.org/abs/1811.10039).
* [nLab: Lawvere–Tierney topology](https://ncatlab.org/nlab/show/Lawvere-Tierney+topology).

## License

Apache 2.0, see `LICENSE`.
