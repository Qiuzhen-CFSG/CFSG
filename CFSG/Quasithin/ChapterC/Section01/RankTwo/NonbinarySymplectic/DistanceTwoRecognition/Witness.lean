module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.Replacement
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry

/-!+# Parabolic placement of the original marked odd-index witness

Restrict the original witness to the component and project through its given
Sp₄ marking. Its odd index supplies an ambient Sylow subgroup, and proper
Sylow-overgroup geometry places the witness in a conjugate point or plane
parabolic. Its core remains the image of the original radical intersect K;
normalization of the smaller replacement image is retained separately.

Source: Aschbacher--Smith C.1.31--32, pp.135--136, and the radical alternatives
required in MS93 (3.7), p.872. This is the placement step, not yet the equality
of the replacement image with one of the source radicals.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : BinaryMS.MS93.CharacteristicReduction K R)

private theorem odd_index_core_normalizer {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hodd : Odd A.index) :
    (normalizer (A.pCoreIn 2 : Set G)).pCoreIn 2 = A.pCoreIn 2 := by
  let N := normalizer (A.pCoreIn 2 : Set G)
  have hAN : A ≤ N := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hi : Odd (A.subgroupOf N).index :=
    hodd.of_dvd_nat (relIndex_dvd_index_of_le hAN)
  have hcore : pCore 2 N ≤ (A.subgroupOf N).pCoreIn 2 :=
    pCore_le_map_pCore_of_prime_not_dvd_index _ hi.not_two_dvd_nat
  have hm := map_mono (f := N.subtype) hcore
  rw [pCoreIn_subgroupOf 2 A N hAN,
    map_subgroupOf_eq_of_le ((A.pCoreIn_le 2).trans hAN)] at hm
  apply le_antisymm hm
  have hl : (A.pCoreIn 2).subgroupOf N ≤ pCore 2 N :=
    le_sSup ⟨inferInstance,(isPGroup_pCoreIn 2 A).of_equiv
      (subgroupOfEquivOfLe (A.pCoreIn 2).le_normalizer).symm⟩
  have hl' := map_mono (f := N.subtype) hl
  rwa [map_subgroupOf_eq_of_le (A.pCoreIn 2).le_normalizer] at hl'

omit [CharP F 2] in
/-- The original radical image, rather than the replacement image, is the
two-core of its full normalizer in the specified symplectic model. -/
theorem original_marked_radical_normalizer_core (d : BinaryMS.MS93.CharacteristicReduction K R) :
    (normalizer ((R.subgroupOf K).map (componentProjection h) :
      Set (Matrix.symplecticGroup (Fin 2) F))).pCoreIn 2 =
        (R.subgroupOf K).map (componentProjection h) := by
  obtain ⟨A,_,hodd,hcore,_⟩ := original_marked_witness h d
  rw [←hcore]
  exact odd_index_core_normalizer A hodd

/-- The original marked witness lies in a genuine symplectic parabolic.
The Sylow subgroup used in the proof is derived from its odd index. -/
theorem original_marked_witness_parabolic :
    ∃ A : Subgroup (Matrix.symplecticGroup (Fin 2) F), A < ⊤ ∧ Odd A.index ∧
      A.pCoreIn 2 = (R.subgroupOf K).map (componentProjection h) ∧
      A ≤ normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
        Set (Matrix.symplecticGroup (Fin 2) F)) ∧
      ∃ u : Matrix.symplecticGroup (Fin 2) F,
        A.map (MulAut.conj u).toMonoidHom ≤ pointParabolic ∨
          A.map (MulAut.conj u).toMonoidHom ≤ planeParabolic := by
  obtain ⟨A,hA,hodd,hcore,hnorm⟩ := original_marked_witness h d
  let P : Sylow 2 A := Classical.choice inferInstance
  have hindex : ¬ 2 ∣ ((P : Subgroup A).map A.subtype).index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hodd.not_two_dvd_nat
  let S := (P.isPGroup'.map A.subtype).toSylow hindex
  have hSA : (S : Subgroup (Matrix.symplecticGroup (Fin 2) F)) ≤ A := map_subtype_le _
  have hlarge : 2 < Nat.card F := by
    rw [h.field_card]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  exact ⟨A,hA,hodd,hcore,hnorm,
    ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover hlarge S A hSA hA.ne⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
