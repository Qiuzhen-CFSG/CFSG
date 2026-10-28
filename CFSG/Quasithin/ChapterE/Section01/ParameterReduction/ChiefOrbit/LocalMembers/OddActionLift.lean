module

public import CFSG.Quasithin.ChapterE.Section01.Inheritance.TwoKernel
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.OddOrbit

/-!
# The literal component-action lift of an odd witness

An odd degree-one witness in the range of the actual core-quotient action
lifts to its full preimage in K N_T(K). The action kernel is a two-group,
and subnormal Sylow intersection supplies the original prescribed Sylow.
The actor remains A intersected with this local group. The final consumer
feeds this witness to the proved odd component-orbit transfer.

The action-image escape premise is explicit: its marked prime-field
geometric producer must identify the actual automizer maximal. This module
proves the transport and does not assert that missing identification.

Source: Aschbacher–Smith E.1.11 and E.2.2, printed pp.213–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

/-- Full-preimage lifting preserves the original local actor and escape. -/
theorem exists_local_odd_escape_of_action (T : Sylow 2 G) {K A M : Subgroup G}
    (hK : K.IsSubnormal) (hc : center (K ⧸ pCore 2 K) = ⊥)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (he :
      let L := localGroup T K
      let S := stabilizer T K
      let ρ := pCoreJoinAction 2 (show S ≤ normalizer K from inf_le_right)
      ∃ I : Subgroup ρ.range,
        IsEMemberAt 1 ((S.subgroupOf L).map ρ.rangeRestrict)
          ((A.subgroupOf L).map ρ.rangeRestrict) I ∧
        ECaseOdd ((A.subgroupOf L).map ρ.rangeRestrict) I ∧
        ¬ I ≤ (M.subgroupOf L).map ρ.rangeRestrict) :
    ∃ P : Subgroup (localGroup T K),
      IsEMemberAt 1 ((stabilizer T K).subgroupOf (localGroup T K))
        (A.subgroupOf (localGroup T K)) P ∧
      ECaseOdd (A.subgroupOf (localGroup T K)) P ∧
      ¬ P.map (localGroup T K).subtype ≤ M := by
  let L := localGroup T K
  let S := stabilizer T K
  let ρ := pCoreJoinAction 2 (show S ≤ normalizer K from inf_le_right)
  obtain ⟨R,hR⟩ := exists_localSylow T K hK
  have hAR : A.subgroupOf L ≤ (R : Subgroup L) := by
    rw [hR]
    intro a ha
    exact ⟨hAT ha,(sup_le K.le_normalizer inf_le_right) a.property⟩
  let : IsElementaryAbelian 2 (A.subgroupOf L) := {
    toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative L A
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
      Subtype.ext (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A:=A) _ a.property))) }
  have hk : IsPGroup 2 ρ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact pCoreJoinAction_kernel_isPGroup 2 inf_le_right (T.isPGroup'.to_le inf_le_left) hc
  obtain ⟨I,hI,ho,hIM⟩ := he
  have hm : IsEMemberAt 1 ((R : Subgroup L).map ρ.rangeRestrict)
      ((A.subgroupOf L).map ρ.rangeRestrict) I := by simpa only [hR] using hI
  obtain ⟨hm,ho,hPM⟩ := odd_escape_comap_of_two_kernel R (A.subgroupOf L) hAR
    ρ.rangeRestrict ρ.rangeRestrict_surjective hk (M.subgroupOf L) I hm ho hIM
  exact ⟨I.comap ρ.rangeRestrict,by simpa only [hR] using hm,ho,
    fun h => hPM (map_le_iff_le_comap.mp h)⟩

/-- The actual odd orbit theorem consumes the lifted witness for the same
member of the original elementary family. -/
theorem not_confined_of_action_odd_escape (T : Sylow 2 G) {K A M : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hcore : pCore 2 G = ⊥)
    (hX : ChiefFactor.IsChief (pResidual 2 G) ⊥)
    (hna : ¬ IsMulCommutative (pResidual 2 G))
    (hK : IsComponentIn K (pResidual 2 G))
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    (he :
      let L := localGroup T K
      let S := stabilizer T K
      let ρ := pCoreJoinAction 2 (show S ≤ normalizer K from inf_le_right)
      ∃ I : Subgroup ρ.range,
        IsEMemberAt 1 ((S.subgroupOf L).map ρ.rangeRestrict)
          ((A.subgroupOf L).map ρ.rangeRestrict) I ∧
        ECaseOdd ((A.subgroupOf L).map ρ.rangeRestrict) I ∧
        ¬ I ≤ (M.subgroupOf L).map ρ.rangeRestrict) :
    ¬ generationTarget 1 T Ω ≤ M := by
  let : IsElementaryAbelian 2 A := hΩ.1 A hA
  obtain ⟨P,hP,ho,hPM⟩ := exists_local_odd_escape_of_action T
    (hK.2.1.trans hK.1 hX.normal_upper.isSubnormal)
    (component_coreQuotient_center_eq_bot hX hna hK) hAT he
  exact fun h => hPM ((local_member_le_generationTarget_of_odd (by decide) T hΩ
    hcore hX hna hK hA hAT hP ho).trans h)

end CFSG.Quasithin.ChapterE.ChiefOrbit
