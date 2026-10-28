module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.Witness
public import Theory.SpecificGroups.SymplecticFour.RadicalParabolics.Exact
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores

/-!
# The three possible original symplectic radical images

The odd-index witness contains the two-core of a full parabolic containing
it, so its own core has nontrivial image in the marked component quotient.
Its previously proved normalizer-core identity makes that image radical.
Exact symplectic radical classification then identifies it, under one
conjugation marking, with a point core, a plane core, or a Sylow two-subgroup.

This supplies the original-radical alternatives needed in MS93 (3.7),
printed pp.872--877. It does not identify the smaller characteristic
replacement image with the original radical image.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : BinaryMS.MS93.CharacteristicReduction K R)

private theorem core_le_of_odd_index_inclusion {G : Type*} [Group G] [Finite G]
    (A P : Subgroup G) (hAP : A ≤ P) (hodd : Odd A.index) :
    P.pCoreIn 2 ≤ A.pCoreIn 2 := by
  have hi : Odd (A.subgroupOf P).index :=
    hodd.of_dvd_nat (relIndex_dvd_index_of_le hAP)
  have hc := map_mono (f := P.subtype)
    (pCore_le_map_pCore_of_prime_not_dvd_index (A.subgroupOf P) hi.not_two_dvd_nat)
  change P.pCoreIn 2 ≤ ((A.subgroupOf P).pCoreIn 2).map P.subtype at hc
  rwa [pCoreIn_subgroupOf 2 A P hAP,
    map_subgroupOf_eq_of_le ((A.pCoreIn_le 2).trans hAP)] at hc

include h d

/-- The original marked radical is nontrivial: its odd-index witness contains
the two-core of a full parabolic containing it. -/
theorem original_marked_radical_ne_bot :
    (R.subgroupOf K).map (componentProjection h) ≠ ⊥ := by
  let := h.quotient_simple
  let : IsSimpleGroup (Sp F) := h.quotientEquiv.symm.isSimpleGroup
  obtain ⟨A,hA,hodd,hcore,hnorm,u,hu⟩ := original_marked_witness_parabolic h d
  let e := MulAut.conj u
  have ho : Odd (A.map e.toMonoidHom).index :=
    hodd.of_dvd_nat (A.index_map_dvd e.surjective)
  intro hz
  have hc : (A.map e.toMonoidHom).pCoreIn 2 = ⊥ := by
    rw [←map_pCoreIn_of_injective 2 A e.toMonoidHom e.injective,hcore,hz,Subgroup.map_bot]
  have impossible (P : Subgroup (Sp F)) (hP : A.map e.toMonoidHom ≤ P)
      (hself : centralizer (P.pCoreIn 2 : Set (Sp F)) ≤ P.pCoreIn 2) : False := by
    have hp : P.pCoreIn 2 = ⊥ := le_bot_iff.mp
      ((core_le_of_odd_index_inclusion _ _ hP ho).trans_eq hc)
    have hall : (⊤ : Subgroup (Sp F)) ≤ ⊥ := by
      intro x _
      apply hp.le
      apply hself
      intro y hy
      have hy' : y = 1 := hp.le hy
      simp [hy']
    exact top_ne_bot (le_bot_iff.mp hall)
  rcases hu with hu | hu
  · apply impossible pointParabolic hu
    change centralizer ((pCore 2 (pointParabolic (F := F))).map pointParabolic.subtype :
      Set (Sp F)) ≤ (pCore 2 (pointParabolic (F := F))).map pointParabolic.subtype
    rw [pointParabolic_core_map_eq_radical h.field_card h.nonbinary]
    exact pointRadicalAmbient_selfCentralizing h.field_card h.nonbinary
  · apply impossible planeParabolic hu
    change centralizer ((pCore 2 (planeParabolic (F := F))).map planeParabolic.subtype :
      Set (Sp F)) ≤ (pCore 2 (planeParabolic (F := F))).map planeParabolic.subtype
    rw [planeParabolic_core_map_eq_radical h.field_card h.nonbinary]
    exact planeRadicalAmbient_selfCentralizing h.field_card h.nonbinary

/-- Radicality of the original image uses its original odd-index witness. -/
theorem original_marked_radical_isPRadical :
    ((R.subgroupOf K).map (componentProjection h)).IsPRadical 2 :=
  ⟨original_marked_radical_ne_bot h d, original_marked_radical_normalizer_core h d⟩

/-- The original radical is exactly a parabolic core or an ambient Sylow
subgroup, with the same conjugation marking on the full normalizer. -/
theorem original_marked_radical_alternatives :
    (∃ u : Sp F,
      (((R.subgroupOf K).map (componentProjection h)).map (MulAut.conj u).toMonoidHom =
          pointRadicalAmbient ∧
        (normalizer ((R.subgroupOf K).map (componentProjection h) : Set (Sp F))).map
          (MulAut.conj u).toMonoidHom = pointParabolic) ∨
      (((R.subgroupOf K).map (componentProjection h)).map (MulAut.conj u).toMonoidHom =
          planeRadicalAmbient ∧
        (normalizer ((R.subgroupOf K).map (componentProjection h) : Set (Sp F))).map
          (MulAut.conj u).toMonoidHom = planeParabolic)) ∨
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h) := by
  rcases radical_normalizer_parabolic_or_sylow _ (original_marked_radical_isPRadical h d)
    h.field_card (by have := h.nonbinary; omega) with ⟨u,hu⟩ | hs
  · left
    refine ⟨u,?_⟩
    have hc := map_pCoreIn_of_injective 2
      (normalizer ((R.subgroupOf K).map (componentProjection h) : Set (Sp F)))
      (MulAut.conj u).toMonoidHom (MulAut.conj u).injective
    rw [original_marked_radical_normalizer_core h d] at hc
    rcases hu with hu | hu
    · refine Or.inl ⟨?_,hu⟩
      rw [hu] at hc
      exact hc.trans (pointParabolic_core_map_eq_radical h.field_card h.nonbinary)
    · refine Or.inr ⟨?_,hu⟩
      rw [hu] at hc
      exact hc.trans (planeParabolic_core_map_eq_radical h.field_card h.nonbinary)
  · exact Or.inr hs

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
