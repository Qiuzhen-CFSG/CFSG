module

public import Theory.SpecificGroups.LieType.ExceptionalSplit.RootFaithfulness
public import Theory.SpecificGroups.LieType.TwistedE6Model
public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.CorootTorus
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Interfaces for exceptional subsystem sections

The matrix carriers in `ExceptionalSplitModels` are central quotients of their
root-generated covers.  A subsystem map therefore has two levels: a map on the
cover and the induced map on the quotient.  This file records that distinction
and supplies the elementary properness lemmas used by the A.2.17 assembly.

The actual cross-family root-datum realizations (for example the folded `F₄`
inside `²E₆`, and the successive `F₄ < E₆ < E₇ < E₈` maps) are intentionally
inputs to the section records below.  The existing concrete carriers do not
contain such maps, and a family tag or an order equality is not a substitute
for one.

Sources: GLS3, §§2.2--2.6 and Aschbacher--Smith, Lemma A.2.17, printed p.39
of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ExceptionalSplit

open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup.StandardRootSystem

universe u v

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {F : Type*} [Field F] [Finite F]

/-! ## Central covers and their quotient maps -/

/-- The root-generated cover used for a split exceptional model. -/
abbrev Cover (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (F : Type*) [Field F] :=
  rootGenerated P b F

/-- The literal central quotient of the root-generated cover. -/
abbrev QuotientModel (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (F : Type*) [Field F] [Finite F] :=
  Model P b F

/-- The cover-to-model map, with its surjectivity exposed at the subsystem layer. -/
def coverProjection : Cover P b F →* QuotientModel P b F :=
  projection P b F

theorem coverProjection_surjective : Function.Surjective (coverProjection (P := P) (b := b) (F := F)) :=
  projection_surjective P b F

theorem coverProjection_kernel :
    (coverProjection (P := P) (b := b) (F := F)).ker =
      Subgroup.center (Cover P b F) :=
  QuotientGroup.ker_mk' _

@[simp] theorem coverProjection_eq_one_iff (x : Cover P b F) :
    coverProjection (P := P) (b := b) (F := F) x = 1 ↔
      x ∈ Subgroup.center (Cover P b F) :=
  projection_eq_one_iff P b F x

/-- A map of central-cover versions and their quotients.

The cover and quotient carriers have separate types.  The square records the
literal compatibility with the two central projections; it does not add a
surjectivity or equality hypothesis that would collapse a proper subsystem
map into an isomorphism of ambient carriers. -/
structure CentralSubsystemMap
    (S Sbar T Tbar : Type*)
    [Group S] [Group Sbar] [Group T] [Group Tbar] where
  cover : S →* T
  quotient : Sbar →* Tbar
  sourceProjection : S →* Sbar
  targetProjection : T →* Tbar
  commute : targetProjection.comp cover = quotient.comp sourceProjection

/-! ## Properness -/

/-- A noncentral element has a proper centralizer. -/
theorem centralizer_singleton_ne_top_of_not_mem_center
    {G : Type*} [Group G] {x : G} (hx : x ∉ Subgroup.center G) :
    Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
  intro htop
  apply hx
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [htop]
    trivial
  have hcomm := (Subgroup.mem_centralizer_iff.mp hg) x (Set.mem_singleton x)
  exact hcomm.symm

/-- A proper embedding presented by its literal range. -/
structure ProperEmbedding (S T : Type*) [Group S] [Group T] where
  hom : S →* T
  injective : Function.Injective hom
  proper : hom.range ≠ ⊤

theorem ProperEmbedding.range_proper {S T : Type*} [Group S] [Group T]
    (d : ProperEmbedding S T) : d.hom.range ≠ ⊤ :=
  d.proper

/-! ## Root-level data, retaining the cover version -/

/-- The centralizer of a parameter-one simple root in the root-generated cover. -/
def coverSimpleRootCentralizer (i : b.support) :
    Subgroup (Cover P b F) :=
  Subgroup.centralizer
    ({elementaryRoot P b F i 1} : Set (Cover P b F))

omit [Finite F] in
theorem coverSimpleRootCentralizer_proper (i : b.support) :
    coverSimpleRootCentralizer (P := P) (b := b) (F := F) i ≠ ⊤ := by
  apply centralizer_singleton_ne_top_of_not_mem_center
  exact elementaryRoot_simple_one_not_mem_center i

/-- The cover centralizer's literal map into the central quotient.  No
surjectivity is asserted: taking the quotient can enlarge the image, and the
quotient-level properness witness is a separate obligation. -/
def coverSimpleRootCentralizer_projection (i : b.support) :
    coverSimpleRootCentralizer (P := P) (b := b) (F := F) i →*
      QuotientModel P b F :=
  (coverProjection (P := P) (b := b) (F := F)).comp
    (coverSimpleRootCentralizer (P := P) (b := b) (F := F) i).subtype

/-- A model-level properness witness for a chosen simple-root centralizer.

The field `noncentral` is the exact quotient-level obligation: it cannot be
derived from noncentrality in the cover without a central-intersection argument. -/
structure ModelCentralizerWitness (i : b.support) where
  noncentral : rootElement P b F i 1 ∉ Subgroup.center (QuotientModel P b F)

def modelSimpleRootCentralizer (i : b.support) :
    Subgroup (QuotientModel P b F) :=
  Subgroup.centralizer
    ({rootElement P b F i 1} : Set (QuotientModel P b F))

theorem modelSimpleRootCentralizer_proper (i : b.support)
    (w : ModelCentralizerWitness (P := P) (b := b) (F := F) i) :
    modelSimpleRootCentralizer (P := P) (b := b) (F := F) i ≠ ⊤ :=
  centralizer_singleton_ne_top_of_not_mem_center w.noncentral

/-! ## Named exceptional carrier aliases -/

local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : Fintype typeE6Roots := Fintype.ofFinite _
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

abbrev f4Cover (F : Type*) [Field F] :=
  Cover typeF4RootPairing typeF4RootPairing_base F

abbrev f4Model (F : Type*) [Field F] [Finite F] :=
  QuotientModel typeF4RootPairing typeF4RootPairing_base F

abbrev e6Cover (F : Type*) [Field F] :=
  Cover typeE6RootPairing typeE6RootPairing_base F

abbrev e6Model (F : Type*) [Field F] [Finite F] :=
  QuotientModel typeE6RootPairing typeE6RootPairing_base F

abbrev e7Cover (F : Type*) [Field F] :=
  Cover typeE7RootPairing typeE7RootPairing_base F

abbrev e7Model (F : Type*) [Field F] [Finite F] :=
  QuotientModel typeE7RootPairing typeE7RootPairing_base F

abbrev e8Cover (F : Type*) [Field F] :=
  Cover typeE8RootPairing typeE8RootPairing_base F

abbrev e8Model (F : Type*) [Field F] [Finite F] :=
  QuotientModel typeE8RootPairing typeE8RootPairing_base F

end ExceptionalSplit

namespace TwistedE6

/-! ## The twisted carrier's central cover -/

variable (p m : ℕ) [Fact p.Prime]

/-- The defining-characteristic fixed-point cover before its central quotient. -/
abbrev centralCover : Type := definingCharacteristicSubgroup p m

/-- The literal central quotient map used by `TwistedE6.Model`. -/
def centralProjection : centralCover p m →* Model p m :=
  toModel p m

theorem centralProjection_surjective :
    Function.Surjective (centralProjection p m) :=
  toModel_surjective p m

theorem centralProjection_kernel :
    (centralProjection p m).ker = Subgroup.center (centralCover p m) :=
  toModel_ker p m

@[simp] theorem centralProjection_eq_one_iff (x : centralCover p m) :
    centralProjection p m x = 1 ↔ x ∈ Subgroup.center (centralCover p m) :=
  toModel_eq_one p m x

end TwistedE6

end
