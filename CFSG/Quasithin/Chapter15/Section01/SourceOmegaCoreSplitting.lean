module
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaSolvableCore
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaResidualGeometry
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# The solvable Omega core and its actual residual splitting

Transport the E.2.17 core from the original H-star subgroup to the ambient
group. The identity T = P C_T(V) makes its image in the chosen normalizer's
faithful Omega quotient equal to the full Sylow image. This discharges the
residual movement, fixed-space and elementary-three image hypotheses of the
cubic splitting theorem for the original smaller quaternion subgroup P.
The final source theorem retains both the H-normal core and the literal
residual X = O²([O²(N),P]) in N = N_M(C_T(V)).

Source: Aschbacher--Smith, 15.1.11, printed p.1089. This proves the valid
centralizer splitting before the later ambient exclusion; no abstract
identification of PX with S4 × S4 is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The actual coordinate quotient has precisely the centralizer kernel. -/
theorem ChosenOmegaCoordinates.ker_eq {N : Subgroup G} {W : Subgroup N}
    [IsElementaryAbelian 2 W] [W.Normal] (c : ChosenOmegaCoordinates N W) :
    c.q.ker = centralizer (W : Set N) := by
  rw [← MultipleFactors.normalRepresentation_ker W]
  ext g
  constructor
  · intro hg
    apply LinearMap.ext
    intro w
    apply c.x.injective
    rw [c.coord]
    rw [show c.q g = 1 from hg]
    rfl
  · intro hg
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := c.x.surjective v
    rw [← c.coord]
    have hv := congrArg (fun f : Module.End (ZMod 2) (Additive W) => f w) hg
    rw [hv]
    rfl

/-- The normal quaternion core, transported through the literal H inclusion. -/
theorem source_fullOmega_solvable_ambient_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable H) (hout : ¬localModule T M ≤ H.pCoreIn 2) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) →
    ∃ P : Subgroup G, P ≤ (T : Subgroup G) ∧ H ≤ normalizer (P : Set G) ∧
      Nonempty (QuaternionCentralProductData P) ∧
      (T : Subgroup G) = P ⊔ ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G)) ∧
      P ⊓ centralizer (localModule T M : Set G) = P ⊓ localModule T M ∧
      ⁅(T : Subgroup G) ⊓ centralizer (localModule T M : Set G),P⁆ ≤
        P ⊓ localModule T M := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  obtain ⟨P,hn,hPT,hd,hprod,hint,hcomm⟩ :=
    source_fullOmega_solvable_normal_core hG T hM hJ hH hs hout ho
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
  refine ⟨Q,hQT,?_,?_,?_,?_,?_⟩
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

/-- The original P has full Sylow image, so the Omega coordinates discharge all residual geometry. -/
theorem source_chosenNormalizer_omega_splitting_of_sylow_product
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) (hVne : V ≠ ⊥)
    (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M)
    (ho : SourceCases.Omega (imageRepresentation M V hMV))
    (P : Subgroup G) (hPT : P ≤ (T : Subgroup G))
    (hprod : (T : Subgroup G) = P ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)))
    (hcomm : ⁅(T : Subgroup G) ⊓ centralizer (V : Set G),P⁆ ≤ V) :
    let N := chosenNormalizer T M V
    let X := (cubicCommutatorResidual (P.subgroupOf N)).map N.subtype
    X ⊓ centralizer (V : Set G) = V ∧
      (T : Subgroup G) ⊓ centralizer (V : Set G) =
        V ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓ centralizer (X : Set G)) ∧
      Disjoint V ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓ centralizer (X : Set G)) ∧
      P ≤ centralizer ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓
        centralizer (X : Set G) : Set G) := by
  dsimp only
  let N := chosenNormalizer T M V
  let W := V.subgroupOf N
  have hred := chosenNormalizer_reduced T hTM hVM hMV hspan
  let := hred.normal
  let := hred.elementary
  let c := Classical.choice
    (source_chosenNormalizer_omega_coordinates hG T hTM hVM hVne hMV hspan ho)
  have hTN : (T : Subgroup G) ≤ N := sylow_le_chosenNormalizer T hTM hMV
  have hPN : P ≤ N := hPT.trans hTN
  have hVN : V ≤ N := module_le_chosenNormalizer T hTM hVM hMV
  let S : Sylow 2 N := T.subtype hTN
  let Q := P.subgroupOf N
  let A : Sylow 2 OrthogonalFourBinary.omega := S.mapSurjective (f := c.q) c.surjective
  have hSW : (S : Subgroup N) = Q ⊔ ((S : Subgroup N) ⊓ centralizer (W : Set N)) := by
    apply (map_injective N.subtype_injective)
    rw [Subgroup.map_sup,map_inf _ _ _ N.subtype_injective,
      map_centralizer_subtype,map_subgroupOf_eq_of_le hVN,
      map_subgroupOf_eq_of_le hPN,show (S : Subgroup N).map N.subtype =
        (T : Subgroup G) from map_subgroupOf_eq_of_le hTN,
      ← inf_assoc,inf_eq_left.mpr hTN]
    exact hprod
  have hQmap : Q.map c.q = (A : Subgroup OrthogonalFourBinary.omega) := by
    change Q.map c.q = (S : Subgroup N).map c.q
    conv_rhs => rw [hSW,Subgroup.map_sup]
    have hk : ((S : Subgroup N) ⊓ centralizer (W : Set N)).map c.q = ⊥ := by
      apply bot_unique
      rw [map_le_iff_le_comap]
      change (S : Subgroup N) ⊓ centralizer (W : Set N) ≤ c.q.ker
      rw [c.ker_eq]
      exact inf_le_right
    rw [hk,sup_bot_eq]
  have hcommN : ⁅pCore 2 N,Q⁆ ≤ W := by
    apply map_subtype_le_map_subtype.mp
    rw [map_commutator,show (pCore 2 N).map N.subtype = _ from
      chosenNormalizer_twoCore T hTM hVM hMV hspan,
      map_subgroupOf_eq_of_le hPN,map_subgroupOf_eq_of_le hVN]
    exact hcomm
  obtain ⟨hm,hf,he,_⟩ := OrthogonalFourBinary.commutatorResidual_geometry
    W c.q c.surjective c.e c.x c.coord Q A hQmap
  have out := source_chosenNormalizer_commutatorResidual_splitting hG T hTM hVM hVne
    hMV hspan Q hcommN hm hf he
  have hQambient : Q.map N.subtype = P := map_subgroupOf_eq_of_le hPN
  rw [hQambient] at out
  exact out

/-- The complete solvable source input for the residual splitting in 15.1.11. -/
theorem source_fullOmega_solvable_residual_splitting
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
    ∃ P : Subgroup G, P ≤ (T : Subgroup G) ∧ H ≤ normalizer (P : Set G) ∧
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
  obtain ⟨P,hPT,hn,hd,hprod,hint,hcomm⟩ :=
    source_fullOmega_solvable_ambient_core hG T hM hJ hH hs hout ho
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
  refine ⟨P,hPT,hn,hd,hprod,hint,hcomm,?_⟩
  exact source_chosenNormalizer_omega_splitting_of_sylow_product hG T hM.1.2
    (localModule_le T hM.1.2) hVne (le_normalizer_conjugateSpanBy _ _) hspan ho
    P hPT hprod (hcomm.trans inf_le_right)

end CFSG.Quasithin.Chapter15.Section01
