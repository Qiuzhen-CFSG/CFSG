module
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaCoreSplitting

/-!
# The marked pair with its original Omega splitting

The two-generator subgroup I and the normal core P=O₂(I) are retained together
through the literal H inclusion. Thus the later quaternion actors and residual
splitting refer to the same P, while the S₃ quotient belongs to I.

Source: Aschbacher--Smith, E.2.17 and 15.1.11, printed pp.229--230 and1089.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original pair and its same ambient quaternion core. -/
theorem source_fullOmega_solvable_marked_ambient_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable H) (hout : ¬localModule T M ≤ H.pCoreIn 2) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) →
    ∃ I : Subgroup H, (localModule T M).subgroupOf H ≤ I ∧
      (∃ g : I, ((localModule T M).subgroupOf H).subgroupOf I ⊔
        (((localModule T M).subgroupOf H).subgroupOf I).map (MulAut.conj g).toMonoidHom = ⊤) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 3) ∧
      (I.pCoreIn 2).Normal ∧
      let P := (I.pCoreIn 2).map H.subtype
      P ≤ (T : Subgroup G) ∧ H ≤ normalizer (P : Set G) ∧
      Nonempty (QuaternionCentralProductData P) ∧
      (T : Subgroup G) = P ⊔ ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G)) ∧
      P ⊓ centralizer (localModule T M : Set G) = P ⊓ localModule T M ∧
      ⁅(T : Subgroup G) ⊓ centralizer (localModule T M : Set G),P⁆ ≤
        P ⊓ localModule T M := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  obtain ⟨I,hWI,hgen,hn,hPT,hd,hprod,hint,hcomm,he⟩ :=
    source_fullOmega_solvable_marked_normal_core hG T hM hJ hH hs hout ho
  let P := I.pCoreIn 2
  let := hn
  let V := localModule T M
  let S : Sylow 2 H := T.subtype hH.1.1.2
  let W := V.subgroupOf H
  let Q := P.map H.subtype
  let d := source_15_1_1_qrcConfiguration hG T hM hH
  have hVH : V ≤ H := (d.module_le_core.trans (left_core_le_sylow d)).trans hH.1.1.2
  have hWmap : W.map H.subtype = V := map_subgroupOf_eq_of_le hVH
  have hSmap : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hQH : Q ≤ H := map_subtype_le P
  have hQT : Q ≤ (T : Subgroup G) := hSmap ▸ map_mono hPT
  change (S : Subgroup H) = P ⊔ ((S : Subgroup H) ⊓ centralizer (W : Set H)) at hprod
  change P ⊓ centralizer (W : Set H) = P ⊓ W at hint
  change ⁅(S : Subgroup H) ⊓ centralizer (W : Set H),P⁆ ≤ P ⊓ W at hcomm
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hCmap : ((S : Subgroup H) ⊓ centralizer (W : Set H)).map H.subtype =
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
    rw [map_inf _ _ _ H.subtype_injective,map_centralizer_subtype,hWmap,hSmap,
      ← inf_assoc,inf_eq_left.mpr hTH]
  refine ⟨I,hWI,hgen,he,hn,hQT,?_,?_,?_,?_,?_⟩
  · simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map,range_subtype] using
      P.le_normalizer_map H.subtype
  · exact hd.map (fun d => d.map (P.equivMapOfInjective H.subtype H.subtype_injective))
  · have h := congrArg (map H.subtype) hprod
    simpa only [Subgroup.map_sup,hSmap,hCmap] using h
  · have h := congrArg (map H.subtype) hint
    change (P ⊓ centralizer (W : Set H)).map H.subtype = (P ⊓ W).map H.subtype at h
    simpa only [map_inf _ _ _ H.subtype_injective,map_centralizer_subtype,hWmap,
      ← inf_assoc,inf_eq_left.mpr (show P.map H.subtype ≤ H from hQH)] using h
  · have h := map_mono (f := H.subtype) hcomm
    rw [map_commutator,hCmap,map_inf _ _ _ H.subtype_injective,hWmap] at h
    exact h

/-- The marked pair, same normal core, and actual residual splitting in 15.1.11. -/
theorem source_fullOmega_solvable_marked_residual_splitting
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable H) (hout : ¬localModule T M ≤ H.pCoreIn 2) :
    let V := localModule T M
    let N := chosenNormalizer T M V
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)) →
    ∃ I : Subgroup H, (localModule T M).subgroupOf H ≤ I ∧
      (∃ g : I, ((localModule T M).subgroupOf H).subgroupOf I ⊔
        (((localModule T M).subgroupOf H).subgroupOf I).map (MulAut.conj g).toMonoidHom = ⊤) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 3) ∧
      (I.pCoreIn 2).Normal ∧
      let P := (I.pCoreIn 2).map H.subtype
      P ≤ (T : Subgroup G) ∧ H ≤ normalizer (P : Set G) ∧
      Nonempty (QuaternionCentralProductData P) ∧
      (T : Subgroup G) = P ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) ∧
      P ⊓ centralizer (V : Set G) = P ⊓ V ∧
      ⁅(T : Subgroup G) ⊓ centralizer (V : Set G),P⁆ ≤ P ⊓ V ∧
      let X := (cubicCommutatorResidual (P.subgroupOf N)).map N.subtype
      X ⊓ centralizer (V : Set G) = V ∧
        (T : Subgroup G) ⊓ centralizer (V : Set G) =
          V ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓ centralizer (X : Set G)) ∧
        Disjoint V ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓ centralizer (X : Set G)) ∧
        P ≤ centralizer ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓
          centralizer (X : Set G) : Set G) := by
  dsimp only
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  obtain ⟨I,hWI,hgen,he,hnI,hPT,hn,hd,hprod,hint,hcomm⟩ :=
    source_fullOmega_solvable_marked_ambient_core hG T hM hJ hH hs hout ho
  let P := (I.pCoreIn 2).map H.subtype
  have hVne : localModule T M ≠ ⊥ := by
    intro hz
    have hZ : centralInvolutions T ≤ localModule T M := le_conjugateSpanBy _ _
    exact centralInvolutions_ne_bot_of_maximal_local T ⟨hM.1.1,hM.1.2⟩
      (bot_unique (hZ.trans_eq hz))
  have hspan : localModule T M = conjugateSpanBy
      (centralInvolutions T ⊓ localModule T M) M := by
    have hZ : centralInvolutions T ≤ localModule T M := le_conjugateSpanBy _ _
    rw [inf_eq_left.mpr hZ]
    rfl
  refine ⟨I,hWI,hgen,he,hnI,hPT,hn,hd,hprod,hint,hcomm,?_⟩
  exact source_chosenNormalizer_omega_splitting_of_sylow_product hG T hM.1.2
    (localModule_le T hM.1.2) hVne (le_normalizer_conjugateSpanBy _ _) hspan ho
    P hPT hprod (hcomm.trans inf_le_right)


end CFSG.Quasithin.Chapter15.Section01
