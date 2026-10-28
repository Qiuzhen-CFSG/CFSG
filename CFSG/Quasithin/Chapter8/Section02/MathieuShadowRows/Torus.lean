module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessTorus
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Transport
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Construction.Prescribed

/-!
# Bounding the actual pair by its torus in the full automizer

Place the pair's odd cyclic torus in an abelian Hall subgroup of the
original maximal overgroup. Its action has the same order, since the
pair's action kernel is a two-group. The full ambient Sylow and Hall
permutation identity descend to the full automizer. Its Cartan parameter
therefore bounds the geometric degree without a quotient-generation rule.
Source: Aschbacher--Smith E.3.37--38 and 8.2.2--3, pp.239--240,714--716.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterB ChapterE HermitianSource
open Offenders.Parabolic Offenders.Parabolic.Construction
open ChapterE.Section06.FixedPointBounds ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Chapter7.NormalizedSource.MathieuGeneration
variable {G : Type*} [Group G] [Finite G]
  {H M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {T : Sylow 2 G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The full automizer bounds the pair's degree when the source maximal
subgroup has Hall control. Faithfulness of its actual torus is proved here. -/
theorem pair_degree_le_automizer_nPrime
    (s : GeometricSelected H T M V I k i S)
    (hTH : (T : Subgroup G) ≤ H)
    (hP : IsMinimalParabolicOver (T.subtype hTH) ⊤)
    (hmax : minimalParabolicMax (T.subtype hTH) hP = M.subgroupOf H)
    (hMV : H ⊓ M ≤ normalizer (V : Set G))
    (hNV : H ⊓ normalizer (V : Set G) ≤ M)
    (hc : HallControl (T.subtype hTH) hP) :
    k ≤ nPrime (Automizer V) := by
  by_cases hk : k ≤ 1
  · exact hk.trans one_le_nPrime
  have hk : 1 < k := by omega
  obtain ⟨y,x,hxy,hy,hq,hx,ho⟩ := s.exists_automizer_torus hk
  let yH : H := ⟨y.val,s.family.le_ambient y.property.2⟩
  have hyM : yH ∈ minimalParabolicMax (T.subtype hTH) hP := by
    rw [hmax]
    exact y.property.1
  have hyH : orderOf yH = 2^k-1 := by
    rw [←Subgroup.orderOf_coe,show (yH : G) = y.val from rfl,Subgroup.orderOf_coe]
    exact hy
  obtain ⟨d,hd⟩ := intrinsic_with_prescribed_cyclic (T.subtype hTH) hP s.positive hc
    (zpowers yH) (zpowers_le.mpr hyM) inferInstance (by rw [Nat.card_zpowers,hyH])
  have hmaxN : minimalParabolicMax (T.subtype hTH) hP =
      (normalizer (V : Set G)).subgroupOf H := by
    rw [hmax]
    ext z
    exact ⟨fun hz => hMV ⟨z.property,hz⟩,fun hz => hNV ⟨z.property,hz⟩⟩
  have hTN : (T : Subgroup G) ≤ normalizer (V : Set G) := by
    intro t ht
    exact (show (⟨t,hTH ht⟩ : H) ∈ (normalizer (V : Set G)).subgroupOf H from
      hmaxN ▸ (minimalParabolicMax_spec (T.subtype hTH) hP).2 ht)
  let w := overlapWitness hTH hTN d hmaxN
  let N := normalizer (V : Set G)
  let yN : N := ⟨y.val,hMV ⟨s.family.le_ambient y.property.2,y.property.1⟩⟩
  have hw : w.cyclicGroup = zpowers yN := by
    apply map_injective N.subtype_injective
    rw [overlapWitness_cyclic_image,hd,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  let qN := V.normalizerMonoidHom.rangeRestrict
  have hqN : qN yN = x := by
    rw [hxy]
    rfl
  have hcard : Nat.card (w.cyclicGroup.map qN) = Nat.card w.cyclicGroup := by
    rw [w.card,hw,MonoidHom.map_zpowers,Nat.card_zpowers,hqN,ho]
  have hfi : Function.Injective (qN.comp w.cyclicGroup.subtype) := by
    have hf := ((qN.subgroupMap_surjective w.cyclicGroup).bijective_of_nat_card_le hcard.ge).1
    intro u v huv
    exact hf (Subtype.ext huv)
  exact (w.map qN V.normalizerMonoidHom.rangeRestrict_surjective hfi).le_nPrime

/-- Apply the native M24 Cartan bound to the full original automizer. -/
theorem m24_pair_degree_le_two_of_hall
    (s : GeometricSelected H T M V I k i S)
    (hTH : (T : Subgroup G) ≤ H)
    (hP : IsMinimalParabolicOver (T.subtype hTH) ⊤)
    (hmax : minimalParabolicMax (T.subtype hTH) hP = M.subgroupOf H)
    (hMV : H ⊓ M ≤ normalizer (V : Set G))
    (hNV : H ⊓ normalizer (V : Set G) ≤ M)
    (hc : HallControl (T.subtype hTH) hP)
    (a : Automizer V ≃* Sporadic.Mathieu.M24) : k ≤ 2 := by
  have hb := pair_degree_le_automizer_nPrime s hTH hP hmax hMV hNV hc
  rw [nPrime_eq_of_mulEquiv a] at hb
  exact hb.trans Models.m24_nPrime_le_two

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
