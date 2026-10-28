module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryParabolicEndpoints
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryGraphFive

/-! In degree five the actual graph interior has the full Aut(GL3(2))
quotient after adjoining the original Sylow. Its original central seed
has reduced normal closure. The native automorphism-group FF obstruction
puts J(S) into the two-core, and original Thompson normalizer control
places the same interior in M. If it centralizes the seed it lies in Mc.
The private import intentionally reuses only reduced_aut_thompson, whose
hypotheses are intrinsic groups and actual reduced actions. -/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- Place the marked degree-five graph interior using its original seed
and actual automorphism quotient, without a component record. -/
theorem PreparedChosenModule.raw_binary_five_graph_interior_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L C : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hnL : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (L : Set G))
    (Q : Sylow 2 L)
    (hQ : (Q : Subgroup L).map L.subtype = ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L)
    (e : (L ⧸ pCore 2 L) ≃* SL(4+1,ZMod 2)) (b : Basis 4)
    (hb : ((((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L).subgroupOf L).map
      (coreFlagMap L e) = cutStabilizer b Set.univ)
    (hC : C = EquivariantLift.lift L (coreFlagMap L e)
      (cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}))
    (hSC : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L ≤ C)
    (hnC : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (C : Set G))
    (hfC : generalizedFitting C = pCore 2 C)
    (ho : ∃ x : ↥((T : Subgroup G) ⊓ centralizer (Z1 : Set G)),
      coreFlagAction L _ hnL e x ∉ MulAut.innerSubgroup _) :
    C ≤ M ⊓ L ∨ C ≤ (centralizer (Z1 : Set G) ⊓ Mc) ⊓ L := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  have hCL : C ≤ L := hC ▸ EquivariantLift.lift_le L _ _
  by_cases hc : C ≤ centralizer (centralInvolutions T : Set G)
  · right
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    exact le_inf (le_inf (hCL.trans hLG) (hc.trans hMc.2)) hCL
  · left
    let H := C ⊔ S
    let K := C.subgroupOf H
    let Z := (centralInvolutions T).subgroupOf H
    let W := normalClosure (Z : Set H)
    let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hnC)
    have hQC : (Q : Subgroup L) ≤ C.subgroupOf L := by
      intro x hx
      exact hSC (hQ ▸ mem_map_of_mem L.subtype hx)
    let t : C.subgroupOf L ≃* C := subgroupOfEquivOfLe hCL
    let R := (Q.subtype hQC).mapSurjective (f := t.toMonoidHom) t.surjective
    have hRS : (R : Subgroup C).map C.subtype ≤ S := by
      rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact (hQ ▸ mem_map_of_mem L.subtype hz).1
    obtain ⟨P,hP⟩ := IsPGroup.exists_sylow_sup_of_coprime_index C S
      (T.isPGroup'.to_le inf_le_left) hnC (R : Subgroup C) R.not_dvd_index hRS
    have hPS : (P : Subgroup H) = S.subgroupOf H := by
      apply map_injective H.subtype_injective
      rw [hP,map_subgroupOf_eq_of_le (show S ≤ H from le_sup_right)]
    have hVT : V ≤ (T : Subgroup G) := by
      let := h.elementary
      let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
      let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
      have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal (T.subtype hM.1.2)
      simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
        map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
    have hZS : centralInvolutions T ≤ S := le_inf (centralInvolutions_le_sylow T)
      ((centralInvolutions_le_centralizer_sylow T).trans
        (centralizer_le ((hZ.trans inf_le_left).trans hVT)))
    let : IsElementaryAbelian 2 (centralInvolutions T) := by
      change IsElementaryAbelian 2 (omegaCenterIn (T : Subgroup G)); infer_instance
    let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf (hZS.trans le_sup_right)
    have hZP : Z ≤ P := by rw [hPS]; exact fun _ hz => hZS hz
    have hZC : Z ≤ centralizer (P : Set H) := by
      intro z hz x hx
      exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
        ((hP ▸ mem_map_of_mem H.subtype hx).1))
    have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
      centralizer_pCore_sup_le 2 C S (hfC ▸ centralizer_generalizedFitting_le C)
        (T.isPGroup'.to_le inf_le_left) hnC
    have hr : IsPReduced 2 W := centralSeed_normalClosure_reduced P Z hZP hZC hchar
    have hm : ⁅W,K⁆ ≠ ⊥ := by
      intro he
      have hh := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
      apply hc
      intro x hx z hz
      exact congrArg Subtype.val (hh (show (⟨x,mem_sup_left hx⟩ : H) ∈ K from hx)
        ⟨z,mem_sup_right (hZS hz)⟩ (le_normalClosure hz))
    let u : K ≃* C := subgroupOfEquivOfLe le_sup_left
    obtain ⟨eC⟩ := hC ▸ RawBinaryParabolic.five_interior_core L e b
    let eK := (QuotientGroup.congr _ _ u (pCore_map_iso 2 u)).trans eC
    have hgen : K ⊔ (P : Subgroup H) = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show C ≤ H from le_sup_left),hP,
        ←MonoidHom.range_eq_map,range_subtype]
    have hquot : IsPGroup 2 (H ⧸ K) :=
      isPGroup_quotient_of_sup_eq_top K (P : Subgroup H) P.isPGroup' hgen
    obtain ⟨eH⟩ := five_interior_extension_aut L S hnL (T.isPGroup'.to_le inf_le_left)
      Q hQ e b hb C hC hnC eC ho
    have hJQ := CaseIComponentData.reduced_aut_thompson W K hr hm eK hquot eH P
    have hJeq := elementaryAbelianMaxJ_eq_of_intermediate (P : Subgroup H) (pCore 2 H)
      hJQ (pCore_isPGroup.le_sylow_of_normal P)
    have hn : K ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) := by
      rw [←hJeq]
      exact le_normalizer_of_normal.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
    have hn' := (map_mono (f := H.subtype) hn).trans
      ((elementaryAbelianMaxJ (P : Subgroup H)).le_normalizer_map H.subtype)
    rw [map_subgroupOf_eq_of_le (show C ≤ H from le_sup_left),
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP] at hn'
    have he := (h.caseI_marked_thompson_control hG T hM hJ hZ).1
    rw [show elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) from he] at hn'
    exact le_inf (hn'.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1) hCL

end CFSG.Quasithin.Chapter15.Section01
