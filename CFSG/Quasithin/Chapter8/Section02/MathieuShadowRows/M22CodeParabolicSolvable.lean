module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeParabolicImage
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSolvable
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The solvable original M22-code parabolic

The selected pair has cubic two-core quotient. The odd-rank bound and the
actual solvable minimal-parabolic catalogue force the residual of H/O₂(H)
to have order three. The cubic divisor survives in the literal image of I,
which therefore contains that residual. Residual lifting gives H=IT,
O²(H)=O²(I), and normalization of the original VA by T.

Consequently O₂(I) is normalized by H. This identifies the literal
intersection kernels and excludes the order-four image of V in the solvable
branch, without assuming either of those conclusions in the residual sieve.
Source: Aschbacher--Smith E.2.1 and 8.2.9, printed pp.215,720--721,
refs/quasithin.pdf. The nonsolvable branch remains separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterB ChapterE HermitianSource Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- The solvable original parabolic has cubic residual. The same pair gives
all source 8.2.9 normalizer conclusions without an image-order premise. -/
theorem selected_m22_code_solvable_parabolic
    {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hsol : Group.IsSolvable H)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (h3 : primeRank 3 H ≤ 1)
    (hpair : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2))) :
    Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3 ∧
      (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
      (H : Set G) = (I : Set G) * (T : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((V ⊔
        (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G) := by
  obtain ⟨t,ht,htP,htM⟩ := h28.minimal
  have hout : ¬ (minimalParabolicMax t htP).pCoreIn 2 ≤ pCore 2 H := by
    intro hc
    apply h28.outside_core
    intro v hv
    obtain ⟨a,ha,he⟩ := h28.le_local_core hv
    have haH : (a : H) ∈ (minimalParabolicMax t htP).pCoreIn 2 := by
      rw [←htM]
      exact ⟨a,ha,rfl⟩
    refine ⟨(a : H),?_,he⟩
    change (a : H) ∈ (M.subgroupOf H).normalCore
    have hh := minimalParabolicTwoCore_le_core t htP (hc haH)
    change (a : H) ∈ (minimalParabolicMax t htP).normalCore at hh
    simpa only [←htM] using hh
  obtain ⟨e⟩ := hpair
  have hcard : Nat.card (I ⧸ pCore 2 I) = 6 := by
    rw [Nat.card_congr (e.trans
      Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm).toEquiv,
      DihedralGroup.nat_card]
  have hdivI : 3 ∣ Nat.card I := (by decide : 3 ∣ 6).trans
    (hcard ▸ (pCore 2 I).index_dvd_card)
  have hdivH := hdivI.trans (card_dvd_of_le s.family.le_ambient)
  have hc := solvable_parabolic_residual_card h28.sqtk t htP hsol hout
    Nat.prime_three (by decide) hdivH h3
  have hcover := Normalizer.ParabolicReduction.quotient_cover_of_prime_residual
    (I.subgroupOf H) Nat.prime_three (by decide) (hc ▸ Nat.prime_three)
    ((Normalizer.ParabolicReduction.RankSieve.odd_divisor_image_twoCore_iff
      (I.subgroupOf H) Nat.prime_three (by decide)).mpr
      (by rwa [Nat.card_congr (subgroupOfEquivOfLe s.family.le_ambient).toEquiv]))
  exact ⟨hc,selected_one_conclusions_of_quotient_cover s hH hTV hcover⟩

/-- Solvability also excludes the order-four image on the same selected pair.
The kernel is the original two-core, not an abstract replacement. -/
theorem selected_m22_code_solvable_core_image
    {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hsol : Group.IsSolvable H)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (h3 : primeRank 3 H ≤ 1)
    (hpair : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2))) :
    I.pCoreIn 2 = I ⊓ H.pCoreIn 2 ∧
      V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2 ∧
      Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
  obtain ⟨_,_,hTR,_,_⟩ := selected_m22_code_solvable_parabolic s h28 hH hsol hTV h3 hpair
  have hTI := (Normalizer.offender_product_normalized I V
    (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) T i i.property s.generate
    hTV hTR (by simpa only [sup_comm] using (selected_one_core_product s).symm)).1
  have hHP : H ≤ normalizer (I.pCoreIn 2 : Set G) := by
    rw [←selected_generates_hstar s hH]
    exact (sup_le I.le_normalizer hTI).trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPQ : I.pCoreIn 2 ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 I) ((pCoreIn_le 2 I).trans s.family.le_ambient) hHP
  have he := selected_one_pair_core_in_hstar_core s (inf_le_right.trans hPQ)
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hB : V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2 := by
    rw [he,←inf_assoc,inf_eq_left.mpr hVI]
  refine ⟨he,hB,?_⟩
  rw [←relIndex_ker,QuotientGroup.ker_mk']
  have hm := relIndex_map_map_of_injective (pCore 2 H) (V.subgroupOf H) H.subtype_injective
  rw [map_subgroupOf_eq_of_le (hVI.trans s.family.le_ambient)] at hm
  rw [←hm,←inf_relIndex_left]
  change (V ⊓ H.pCoreIn 2).relIndex V = 2
  rw [←hB]
  exact selected_one_core_index s

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
