module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.PointCommutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.QuotientInputs
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.NoncentralChiefRefinement.Actions
public import CFSG.Quasithin.ChapterC.Section01.ChiefSections.A7Quotient
public import Theory.SpecificGroups.Alternating.FiveChiefDegree
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.AlternatingBound.SourceCases

/-!
# The A₇ chief-factor bound

Every complete chief series of a two-perfect A₅ extension embedded in an
A₇ short group with block module of order at most 64 has at most one
noncentral binary factor. The actual intersection filtration embeds any two
counted sections in the block module, while the A₅ action makes each section
have order at least 16. The final arithmetic is `16 * 16 > 2 ^ 6`.

`count_le_one_of_embedding` and `subgroup_count_le_one` discharge the structural
premises of the preserved conditional arithmetic interface. The original K
consumer `every_complete_K_chief_count_le_one_of_c27` also derives the module
bound from the full C.2.7 alternatives, retaining ordinary and exceptional A₇
blocks. It has no additional degree, filtration, or block-type premise.

The quotient maps in the application below are the actual maps on `K` and
`Lᵤ`.  In particular, the A₅ quotient is `K/O₂(K)` obtained from `qH` and
`K_image`, while the A₇ quotient is the supplied `Lᵤ/O₂(Lᵤ)` map.  The star
quotient occurring in C.2.7 is not identified with this latter quotient.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
 C.1.7, C.1.22 and 14.7.68(2), printed pp.129, 1071--1072.
-/

@[expose] public section
noncomputable section

open Subgroup
open NoncentralChiefRefinement
open Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

open Chapter12.Section08

universe u

namespace AlternatingBound

/- The direct cardinal statement is useful in the final arithmetic step and
   keeps the filtration interface independent of a choice of coordinates. -/
private theorem card_pair_le_of_injective
    {E J : Type u} [Group E] [Group J] [Finite (ChapterC.BlockModule E)]
    {s : ChiefSeries J} {i j : Fin s.length}
    (f : Section (s i.castSucc) (s i.succ) ×
      Section (s j.castSucc) (s j.succ) → ChapterC.BlockModule E)
    (hf : Function.Injective f) :
    Nat.card (Section (s i.castSucc) (s i.succ)) *
        Nat.card (Section (s j.castSucc) (s j.succ)) ≤
      Nat.card (ChapterC.BlockModule E) := by
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod] using h

/- A complete series has more than one counted factor exactly when it has two
   distinct counted indices.  We keep this local because the public count API
   intentionally exposes only the cardinality of its subtype. -/
private theorem one_lt_count_iff {J : Type u} [Group J]
    (s : ChiefSeries J) :
    1 < s.noncentralTwoCount ↔
      ∃ i j : Fin s.length, i ≠ j ∧
        IsNoncentralTwo (s i.castSucc) (s i.succ) ∧
        IsNoncentralTwo (s j.castSucc) (s j.succ) := by
  classical
  let _ : Fintype {i : Fin s.length //
      IsNoncentralTwo (s i.castSucc) (s i.succ)} := Fintype.ofFinite _
  rw [ChiefSeries.noncentralTwoCount, Nat.card_eq_fintype_card,
    Fintype.one_lt_card_iff]
  constructor
  · rintro ⟨i, j, hij⟩
    exact ⟨i.1, j.1, fun he => hij (Subtype.ext he), i.2, j.2⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩,
      fun he => hij (congrArg Subtype.val he)⟩

/- The source's filtration/action claims.  `pairMap` is the literal map from
   two relative chief sections into the block module.  Its injectivity is the
   structural part proved from the intersection filtration; it does not assert
   normality of `J` in `E`. -/
structure Input (E J : Type u) [Group E] [Group J] [Finite E] [Finite J] where
  short : ChapterC.IsShort E
  quotientE : Nonempty ((E ⧸ pCore 2 E) ≃* alternatingGroup (Fin 7))
  module_bound : Nat.card (ChapterC.BlockModule E) ≤ 2 ^ 6
  subgroup : Subgroup E
  embedding : J →* subgroup
  embedding_injective : Function.Injective embedding
  perfect : IsPPerfect 2 J
  quotientJ : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
  factor_card : ∀ (s : ChiefSeries J) (i : Fin s.length),
    IsNoncentralTwo (s i.castSucc) (s i.succ) →
      16 ≤ Nat.card (Section (s i.castSucc) (s i.succ))
  pairMap : ∀ (s : ChiefSeries J) (i j : Fin s.length),
    i ≠ j → IsNoncentralTwo (s i.castSucc) (s i.succ) →
      IsNoncentralTwo (s j.castSucc) (s j.succ) →
      Section (s i.castSucc) (s i.succ) ×
        Section (s j.castSucc) (s j.succ) → ChapterC.BlockModule E
  pairMap_injective : ∀ (s : ChiefSeries J) (i j : Fin s.length)
    (hij : i ≠ j) (hi : IsNoncentralTwo (s i.castSucc) (s i.succ))
    (hj : IsNoncentralTwo (s j.castSucc) (s j.succ)),
    Function.Injective (pairMap s i j hij hi hj)

/-- Two distinct noncentral binary sections force more than the available
block-module cardinality. -/
theorem count_le_one {E J : Type u} [Group E] [Group J] [Finite E] [Finite J]
    (h : Input E J) (s : ChiefSeries J)
    (_h0 : s.head = ⊥) (_h1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  by_contra hcount
  have hgt : 1 < s.noncentralTwoCount := by omega
  obtain ⟨i, j, hij, hi, hj⟩ := one_lt_count_iff s |>.mp hgt
  have hpair := card_pair_le_of_injective
    (h.pairMap s i j hij hi hj) (h.pairMap_injective s i j hij hi hj)
  have hlow : 16 * 16 ≤
      Nat.card (Section (s i.castSucc) (s i.succ)) *
        Nat.card (Section (s j.castSucc) (s j.succ)) :=
    Nat.mul_le_mul (h.factor_card s i hi) (h.factor_card s j hj)
  have hupper :
      Nat.card (Section (s i.castSucc) (s i.succ)) *
        Nat.card (Section (s j.castSucc) (s j.succ)) ≤ 2 ^ 6 :=
    hpair.trans h.module_bound
  norm_num at hupper hlow
  omega

/- Both C.1.7/C.1.22 A₇ block possibilities fit the six-dimensional
   ordinary-module bound used by the chief obstruction. -/

/-- Both C.1.7/C.1.22 A₇ block possibilities fit the six-dimensional
ordinary-module bound used by the chief obstruction. -/
theorem module_card_le_of_a7
    {E : Type u} [Group E]
    (h : ChapterC.IsAlternatingBlock E 7 ∨
      ChapterC.IsExceptionalA7Block E) :
    Nat.card (ChapterC.BlockModule E) ≤ 2 ^ 6 := by
  rcases h with h | h
  · rw [h.module_card_odd (by decide)]
  · rw [h.module_card]
    norm_num

/-- The structural bound, with the degree and intersection claims discharged
from the original embedding and both actual core markings. -/
theorem count_le_one_of_embedding {E J : Type u} [Group E] [Group J]
    [Finite E] [Finite J] (short : ChapterC.IsShort E)
    (ι : J →* E) (hι : Function.Injective ι)
    (eE : (E ⧸ pCore 2 E) ≃* alternatingGroup (Fin 7))
    (eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (hp : IsPPerfect 2 J) (hcard : Nat.card (ChapterC.BlockModule E) ≤ 2 ^ 6)
    (s : ChiefSeries J) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  let pair := ChapterC.a7_chiefPairEmbedding ι hι eE eJ hp
  apply count_le_one (E := E) (J := J) (s := s) (h := {
    short := short
    quotientE := ⟨eE⟩
    module_bound := hcard
    subgroup := ι.range
    embedding := ι.rangeRestrict
    embedding_injective := fun x y he => hι (congrArg Subtype.val he)
    perfect := hp
    quotientJ := ⟨eJ⟩
    factor_card := fun t i hi => alternatingGroup.FiveChiefDegree.section_card_ge_sixteen
      hp eJ (t i.castSucc) (t i.succ) hi
    pairMap := fun t i j hij hi hj => pair t i j hij hi hj
    pairMap_injective := fun t i j hij hi hj => (pair t i j hij hi hj).injective }) hs0 hs1

/-- Every complete actual chief series of a possibly nonnormal subgroup J
has at most one noncentral binary chief factor. -/
theorem subgroup_count_le_one {E : Type u} [Group E]
    (short : ChapterC.IsShort E)
    (eE : (E ⧸ pCore 2 E) ≃* alternatingGroup (Fin 7))
    (hcard : Nat.card (ChapterC.BlockModule E) ≤ 2 ^ 6)
    (J : Subgroup E) (hp : IsPPerfect 2 J)
    (eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (s : ChiefSeries J) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  let := short.finite
  exact count_le_one_of_embedding short J.subtype J.subtype_injective eE eJ hp hcard s hs0 hs1

end AlternatingBound

namespace Data

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u}
  [AddCommGroup W] [Module (ZMod 2) W]

variable (d : Data T L V F W)

/- The inclusion is the literal subgroup inclusion; no normality of `K` in
   `Lᵤ` is introduced. -/
def KToFixedComponent
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    K F →* Lu := inclusion h.larger.le

@[simp] theorem KToFixedComponent_apply
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (k : K F) :
    d.KToFixedComponent u h k = ⟨(k : G), h.larger.le k.property⟩ := rfl

/-- The literal K-to-`Lᵤ/O₂(Lᵤ)` map used when comparing the two quotient
identifications. -/
def KToFixedComponentCoreQuotient
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    K F →* (Lu ⧸ pCore 2 Lu) :=
  (QuotientGroup.mk' (pCore 2 Lu)).comp (d.KToFixedComponent u h)

/-- The original marking gives the actual A₅ quotient of `K/O₂(K)`. -/
def KCoreA5 : (K F ⧸ pCore 2 (K F)) ≃* alternatingGroup (Fin 5) :=
  d.KCoreAlternatingFive

@[simp] theorem KCoreA5_mk
    (k : K F) :
    d.KCoreA5 (QuotientGroup.mk' (pCore 2 (K F)) k) = d.KToAlternatingFive k :=
  d.KCoreAlternatingFive_mk k

theorem a7_module_bound
    (u : F.U) {Lu : Subgroup G} (_h : Nonquasisimple.Case d u Lu)
    (block : ChapterC.IsAlternatingBlock Lu 7 ∨
      ChapterC.IsExceptionalA7Block Lu) :
    Nat.card (ChapterC.BlockModule Lu) ≤ 2 ^ 6 := by
  exact AlternatingBound.module_card_le_of_a7 block

/- This is the actual consumer.  The `pairMap` and factor lower bound are the
 source filtration/action claims; all quotient and C.2.7 data are retained in
 the theorem's inputs so that the consumer cannot silently switch to a star
 quotient or to an unmarked A₅ family. -/
theorem every_complete_K_chief_count_le_one
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (_c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Conclusion
      KnownSimple.IsKnownSimple (d.fixedCentralizer u) Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u : Subgroup G))
    (hLu : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7)))
    (block : ChapterC.IsAlternatingBlock Lu 7 ∨
      ChapterC.IsExceptionalA7Block Lu)
    (factor_card : ∀ (s : ChiefSeries (K F)) (i : Fin s.length),
      IsNoncentralTwo (s i.castSucc) (s i.succ) →
        16 ≤ Nat.card (Section (s i.castSucc) (s i.succ)))
    (pairMap : ∀ (s : ChiefSeries (K F)) (i j : Fin s.length),
      i ≠ j → IsNoncentralTwo (s i.castSucc) (s i.succ) →
      IsNoncentralTwo (s j.castSucc) (s j.succ) →
      Section (s i.castSucc) (s i.succ) ×
        Section (s j.castSucc) (s j.succ) → ChapterC.BlockModule Lu)
    (pairMap_injective : ∀ (s : ChiefSeries (K F)) (i j : Fin s.length)
      (hij : i ≠ j) (hi : IsNoncentralTwo (s i.castSucc) (s i.succ))
      (hj : IsNoncentralTwo (s j.castSucc) (s j.succ)),
      Function.Injective (pairMap s i j hij hi hj))
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  let hKle : K F ≤ Lu := h.larger.le
  let hiA5 : Nonempty ((K F ⧸ pCore 2 (K F)) ≃*
      alternatingGroup (Fin 5)) := ⟨d.KCoreA5⟩
  let hiA7 : Nonempty ((Lu ⧸ pCore 2 Lu) ≃*
      alternatingGroup (Fin 7)) := hLu
  let hi : AlternatingBound.Input Lu (K F) := {
    short := (block.elim (fun hb => hb.2.1) (fun hb => hb.1))
    quotientE := hiA7
    module_bound := AlternatingBound.module_card_le_of_a7 block
    subgroup := (K F).subgroupOf Lu
    embedding := (subgroupOfEquivOfLe hKle).symm.toMonoidHom
    embedding_injective := (subgroupOfEquivOfLe hKle).symm.injective
    perfect := K_twoPerfect F
    quotientJ := hiA5
    factor_card := factor_card
    pairMap := pairMap
    pairMap_injective := pairMap_injective }
  exact AlternatingBound.count_le_one hi s hs0 hs1

/-- C.2.7 on the original groups supplies the order bound for the actual
block module, retaining both ordinary and exceptional A₇ blocks. -/
theorem a7_module_bound_of_c27
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Conclusion
      KnownSimple.IsKnownSimple (d.fixedCentralizer u) Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u : Subgroup G))
    (hLu : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7))) :
    Nat.card (ChapterC.BlockModule Lu) ≤ 2 ^ 6 :=
  AlternatingBound.module_card_le_of_c27_a7 c27
    (d.fixedCore_normalizes_component u h) hLu.some

/-- The A₇ upper bound in 14.7.68(2), with every degree, filtration and
module-bound premise discharged. The block is relative to the original
fixed centralizer. K embeds by literal inclusion, without a normality
assumption, and its A₅ marking is induced by qH with kernel exactly O₂(K).
The full source C.2.7 conclusion remains on Gᵤ, Lᵤ, Rᵤ and H ∩ Gᵤ. -/
theorem every_complete_K_chief_count_le_one_of_c27
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Conclusion
      KnownSimple.IsKnownSimple (d.fixedCentralizer u) Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u : Subgroup G))
    (block : ChapterC.IsBlock (Lu.subgroupOf (d.fixedCentralizer u)))
    (hLu : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7)))
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  have short : ChapterC.IsShort Lu :=
    block.short.of_mulEquiv (subgroupOfEquivOfLe h.le_centralizer)
  exact AlternatingBound.count_le_one_of_embedding short
    (d.KToFixedComponent u h) (inclusion_injective h.larger.le)
    hLu.some d.KCoreA5 (K_twoPerfect F) (d.a7_module_bound_of_c27 u h c27 hLu)
    s hs0 hs1

end Data

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

