module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CubicFiltration
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CartanCubicCounts

/-!
# The cubic filtration of the original orbit

The full original normalizer in H acts on the conjugate span and on its
literal seed V. Their coordinates intertwine the actual full-automizer map.
Intersecting an arbitrary H-chief series with this seed gives its original
filtration. Cubic exactness adds its displacements to six; central H-chief
intervals contribute zero. When the span has two noncentral chief factors,
some induced seed section must therefore have cubic codimension at least
three. This is an assertion about sections of the original V, not a direct
comparison of constituent counts for different modules.

The chosen cubic has order three in the faithful whole-span image. No
order-three assertion is made for its upstairs representative. The natural
fixed-space estimates that contradict the large section remain separate.
Source: Aschbacher--Smith,3.1.9(6), printed p.578, used in8.2.2(1), p.715,
refs/quasithin.pdf. The original chosen-module application is
`NonFFSourceMathieuShadowRows/M22CodeCubicFiltration`.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterD ChapterE
open MathieuCode.NormalizedShadowRows.CubicFiltration
open BinaryLinearThree.ParabolicCyclic.ChiefCounts hiding sectionRepresentation
variable {G : Type*} [Group G] (H V : Subgroup G)
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]

/-- The original normalizer inside the original parabolic. -/
abbrev seedNormalizer := (normalizer (V : Set G)).subgroupOf H

/-- Its original action on the whole conjugate span. -/
def seedNormalizerAction :=
  (normalRepresentation ((conjugateSpan H V).subgroupOf H)).comp (seedNormalizer H V).subtype

/-- The unchanged original seed, invariant under its full normalizer in H. -/
def originalSeed : Subrepresentation (seedNormalizerAction H V) where
  toSubmodule := spanSeed H V
  apply_mem_toSubmodule x := by
    intro v hv
    exact (mem_normalizer_iff.mp x.property _).mp hv

/-- The original action map into the full automizer. -/
def seedNormalizerHom : seedNormalizer H V →* Automizer V :=
  V.normalizerMonoidHom.rangeRestrict.comp {
    toFun := fun x => ⟨((x : H) : G),x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

variable [IsElementaryAbelian 2 V]

/-- Coordinates only change subtype presentation of the original seed. -/
def originalSeedCoordinates (hVH : V ≤ H) :
    Additive V ≃ₗ[ZMod 2] (originalSeed H V).toSubmodule := by
  let e : Additive V ≃+ (originalSeed H V).toSubmodule := {
    toFun := fun v => ⟨spanSeedVector H V hVH v.toMul,v.toMul.property⟩
    invFun := fun v => Additive.ofMul ⟨((v.val.toMul : H) : G),v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }
  exact { e with map_smul' := ZMod.map_smul e }

/-- The original normalizer action agrees with the full automizer action. -/
theorem originalSeedCoordinates_equivariant (hVH : V ≤ H)
    (x : seedNormalizer H V) (v : Additive V) :
    originalSeedCoordinates H V hVH (automizerRepresentation V (seedNormalizerHom H V x) v) =
      (originalSeed H V).toRepresentation x (originalSeedCoordinates H V hVH v) := rfl

/-- Restriction of an actual chief-series term to the original normalizer. -/
def normalizerTerm (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin (s.series.length+1)) : Subrepresentation (seedNormalizerAction H V) where
  toSubmodule := (s.linearTerm i).toSubmodule
  apply_mem_toSubmodule x := (s.linearTerm i).apply_mem_toSubmodule (x : H)

/-- The literal section of the original seed induced by an H-chief interval. -/
def originalSeedFactor (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) :=
  Representation.BinaryOffender.sectionRepresentation (originalSeed H V).toRepresentation
    (seedTerm (seedNormalizerAction H V) (originalSeed H V) (normalizerTerm H V s i.castSucc))
    (seedTerm (seedNormalizerAction H V) (originalSeed H V) (normalizerTerm H V s i.succ))

variable [Finite G]

/-- Fixed codimension six is transported to the unchanged original seed. -/
theorem originalSeed_cubic_codim_six (hVH : V ≤ H)
    (b : H) (hn : (b : G) ∈ normalizer (V : Set G))
    (hz : orderOf (V.normalizerMonoidHom.rangeRestrict ⟨(b : G),hn⟩) = 3)
    (hc : HasCount ((automizerRepresentation V).comp
      (zpowers (V.normalizerMonoidHom.rangeRestrict ⟨(b : G),hn⟩)).subtype) 3) :
    fixedCodim (originalSeed H V).toRepresentation (zpowers ⟨b,hn⟩) = 6 := by
  let z := V.normalizerMonoidHom.rangeRestrict ⟨(b : G),hn⟩
  have hZ : Nat.card (zpowers z) = 3 := (Nat.card_zpowers z).trans hz
  have hh := fixedCodim_of_count ((automizerRepresentation V).comp (zpowers z).subtype) hZ hc
  have hcod : fixedCodim (automizerRepresentation V) (zpowers z) = 6 := by
    unfold fixedCodim at hh
    rw [fixedSpace_comp_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    exact hh
  have he := fixedCodim_map_equivariant (originalSeed H V).toRepresentation
    (automizerRepresentation V) (seedNormalizerHom H V)
    (originalSeedCoordinates H V hVH).symm (fun _ _ => rfl) (zpowers ⟨b,hn⟩)
  rw [MonoidHom.map_zpowers] at he
  exact he.trans hcod

/-- Exact cubic displacement on the filtration of V induced by any actual H-chief series. -/
theorem sum_originalSeedFactor_codim (hVH : V ≤ H)
    (b : H) (hn : (b : G) ∈ normalizer (V : Set G))
    (hb : orderOf (actionHom (normalRepresentation ((conjugateSpan H V).subgroupOf H)) b) = 3)
    (hz : orderOf (V.normalizerMonoidHom.rangeRestrict ⟨(b : G),hn⟩) = 3)
    (hc : HasCount ((automizerRepresentation V).comp
      (zpowers (V.normalizerMonoidHom.rangeRestrict ⟨(b : G),hn⟩)).subtype) 3)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) :
    ∑ i : Fin s.series.length,
      fixedCodim (originalSeedFactor H V s i) (zpowers ⟨b,hn⟩) = 6 := by
  let τ := normalRepresentation ((conjugateSpan H V).subgroupOf H)
  have hp : actionHom τ b ^ 3 = 1 := by rw [←hb]; exact pow_orderOf_eq_one _
  have hcube : (seedNormalizerAction H V ⟨b,hn⟩)^3 = 1 := by
    change (τ b)^3 = 1
    simpa only [map_pow, map_one, imageRepresentation_actionHom] using
      congrArg (Representation.BinaryOffender.imageRepresentation τ) hp
  have hmono : Monotone (normalizerTerm H V s) := by
    intro i j hij v hv
    exact s.linearTerm_mono hij hv
  have h0 : normalizerTerm H V s 0 = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    change (s.linearTerm 0).toSubmodule = _
    rw [s.linearTerm_zero]
    rfl
  have h1 : normalizerTerm H V s (Fin.last s.series.length) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    change (s.linearTerm (Fin.last s.series.length)).toSubmodule = _
    rw [s.linearTerm_last]
    rfl
  exact (sum_seed_codim (seedNormalizerAction H V) (originalSeed H V)
    (normalizerTerm H V s) hmono h0 h1 ⟨b,hn⟩ hcube).trans
      (originalSeed_cubic_codim_six H V hVH b hn hz hc)

omit [IsElementaryAbelian 2 V] in
set_option backward.isDefEq.respectTransparency false in
/-- Central H-chief intervals give zero contribution to the original seed filtration. -/
theorem originalSeedFactor_codim_zero
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length)
    (hi : s.Central i) (b : H) (hn : (b : G) ∈ normalizer (V : Set G)) :
    fixedCodim (originalSeedFactor H V s i) (zpowers ⟨b,hn⟩) = 0 := by
  apply seed_section_codim_zero
  intro v
  change s.linearFactor i b v = v
  apply (s.factorLinearEquiv i).injective
  rw [s.factorLinearEquiv_equivariant]
  exact congrArg Additive.ofMul ((s.central_iff_action i).mp hi b
    (s.factorLinearEquiv i v).toMul)

/-- Three original cubic factors force an induced section of codimension at least three
on one of the two noncentral H-chief intervals. -/
theorem exists_large_originalSeedFactor (hVH : V ≤ H)
    (b : H) (hn : (b : G) ∈ normalizer (V : Set G))
    (hb : orderOf (actionHom (normalRepresentation ((conjugateSpan H V).subgroupOf H)) b) = 3)
    (hz : orderOf (V.normalizerMonoidHom.rangeRestrict ⟨(b : G),hn⟩) = 3)
    (hc : HasCount ((automizerRepresentation V).comp
      (zpowers (V.normalizerMonoidHom.rangeRestrict ⟨(b : G),hn⟩)).subtype) 3)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (hs : s.noncentralCount = 2) :
    ∃ i : Fin s.series.length, ¬ s.Central i ∧
      3 ≤ fixedCodim (originalSeedFactor H V s i) (zpowers ⟨b,hn⟩) := by
  classical
  by_contra! hsmall
  have hsum := sum_originalSeedFactor_codim H V hVH b hn hb hz hc s
  have hle : (∑ i : Fin s.series.length,
      fixedCodim (originalSeedFactor H V s i) (zpowers ⟨b,hn⟩)) ≤
      ∑ i : Fin s.series.length, 2 * (if ¬ s.Central i then 1 else 0) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : s.Central i
    · rw [if_neg (not_not.mpr hi),mul_zero,originalSeedFactor_codim_zero H V s i hi b hn]
    · rw [if_pos hi,mul_one]
      have hh := hsmall i hi
      omega
  have he : (∑ i : Fin s.series.length, if ¬ s.Central i then 1 else 0) =
      s.noncentralCount := by
    rw [SeriesOn.noncentralCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp only [Finset.sum_boole,Nat.cast_id]
  rw [← Finset.mul_sum,he,hs,hsum] at hle
  omega

end CFSG.Quasithin.Chapter8.MathieuShadowRows
