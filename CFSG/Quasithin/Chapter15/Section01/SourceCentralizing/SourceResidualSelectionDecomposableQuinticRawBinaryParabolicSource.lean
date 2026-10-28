module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryParabolicFive
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryLinearIntersection
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryParabolicCore

/-! The actual native nodes, or graph interior/endpoint pair, generate the
same original component. Each generator is placed using its literal source
parabolic data or the reduced degree-five automorphism action. Hence the
two original intersections generate L. The original quintic cubic residual
then puts both intersections in Mc and contradicts L's escape. The final
endpoint starts with the actual B.5 normalizer image and its full central
core map; no star/normalizer identification or generation premise is used. -/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- The literal binary core forces generation by the two original
intersections; generation is proved from native nodes and their placement. -/
theorem PreparedChosenModule.raw_binary_linear_original_intersections_generate
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hf : generalizedFitting L = pCore 2 L)
    {n : ℕ} (hn : n=4 ∨ n=5) (e : (L ⧸ pCore 2 L) ≃* SL(n,ZMod 2)) :
    (M ⊓ L) ⊔ ((centralizer (Z1 : Set G) ⊓ Mc) ⊓ L) = L := by
  obtain ⟨m,hm,rfl⟩ : ∃ m, (m=3 ∨ m=4) ∧ n=m+1 := by
    rcases hn with rfl | rfl
    · exact ⟨3,Or.inl rfl,rfl⟩
    · exact ⟨4,Or.inr rfl,rfl⟩
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let J := (M ⊓ L) ⊔ ((centralizer (Z1 : Set G) ⊓ Mc) ⊓ L)
  have hnL := h.raw_binary_linear_sylow_normalizes hG T hZ hZne hL hq hn e
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hL.2
  have hQS : (Q : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show S ⊓ L ≤ L from inf_le_right)]
    exact hQ
  obtain ⟨b,hb,hctrl⟩ := exists_core_flag_control L S hnL Q hQ hm e
  have hbQ : (Q : Subgroup L).map (coreFlagMap L e) = cutStabilizer b Set.univ := by
    rw [hQS]; exact hb
  have hS : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  have hplace {P : Subgroup G} (hPL : P ≤ L) (hnP : S ≤ normalizer (P : Set G))
      (hfit : generalizedFitting P = pCore 2 P)
      (he : Nonempty (((P ⊔ S : Subgroup G) ⧸ pCore 2 (P ⊔ S : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) ∨
        Nonempty (((P ⊔ S : Subgroup G) ⧸ pCore 2 (P ⊔ S : Subgroup G)) ≃*
          RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
      (hno : ¬CaseIComponentData.IsAThreeProduct P) : P ≤ J := by
    rcases h.raw_parabolic_placement_of_sylow_normalizes hG T hM hJ hu hZ hZne
      hSyl hL.1 hPL hnP hfit he hno with hp | hp
    · exact hp.trans le_sup_left
    · exact hp.trans le_sup_right
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  rcases hctrl with hi | ⟨ho,hctrl⟩
  · have hn (i : Fin m) :
        EquivariantLift.lift L (coreFlagMap L e) (minimalParabolic b i) ≤ J := by
      let P := EquivariantLift.lift L (coreFlagMap L e) (minimalParabolic b i)
      obtain ⟨hfit,⟨eqP⟩,hno⟩ := RawBinaryParabolic.node_data L Q hf (by omega) e b hbQ i
      have hnP : S ≤ normalizer (P : Set G) := hi.2 {i}ᶜ
      exact hplace (EquivariantLift.lift_le _ _ _) hnP hfit
        (Or.inl (NormalSymmetricThreeExtension.normalized_join P S hnP eqP hS)) hno
    calc
      L = ⨆ i : Fin m, EquivariantLift.lift L (coreFlagMap L e) (minimalParabolic b i) :=
        (RawBinaryParabolic.nodes_generate L (by omega) e b).symm
      _ ≤ J := iSup_le hn
  · let C := EquivariantLift.lift L (coreFlagMap L e)
      (cutStabilizer b {i | i.val=0 ∨ i.val=m-1})
    let E := EquivariantLift.lift L (coreFlagMap L e)
      (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}ᶜ)
    obtain ⟨hCL,hEL,hSC,hSE,hnC,hnE,hCf,hEf,⟨eE⟩,hgen⟩ :=
      RawBinaryParabolic.graph_pair L S hnL Q hQ hf hm e b hb hctrl
    have hEq := endpoint_extension_wreath L S hnL hS Q hQ hm e b hb E rfl hnE eE ho
    have hE : E ≤ J := by
      apply hplace hEL.le hnE hEf (Or.inr hEq)
      rcases hm with rfl | rfl
      · exact RawBinaryParabolic.four_endpoint_not_aThree L hf e b
      · exact RawBinaryParabolic.five_endpoint_not_aThree L e b
    have hC : C ≤ J := by
      rcases hm with rfl | rfl
      · have hc : C = EquivariantLift.lift L (coreFlagMap L e) (minimalParabolic b (1 : Fin 3)) := by
          change EquivariantLift.lift _ _ (cutStabilizer b _) =
            EquivariantLift.lift _ _ (cutStabilizer b _)
          congr 2
          ext i
          fin_cases i <;> decide
        obtain ⟨_,⟨eqC⟩,hno⟩ := RawBinaryParabolic.node_data L Q hf (by decide) e b hbQ (1 : Fin 3)
        rw [←hc] at eqC hno
        exact hplace hCL.le hnC hCf
          (Or.inl (NormalSymmetricThreeExtension.normalized_join C S hnC eqC hS)) hno
      · rcases h.raw_binary_five_graph_interior_placement hG T hM hJ hu hZ hL.1 hnL
          Q hQ e b hb (show C = _ from rfl) hSC hnC hCf ho with hp | hp
        · exact hp.trans le_sup_left
        · exact hp.trans le_sup_right
    calc
      L = C ⊔ E := hgen.symm
      _ ≤ J := sup_le hC hE

/-- The original quintic cubic residual and the proved binary generation
exclude the literal binary core on this same component. -/
theorem PreparedChosenModule.raw_not_binary_linear_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hf : generalizedFitting L = pCore 2 L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc)
    (hcubic : (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤ centralizer (V : Set G))
    {n : ℕ} (hn : n=4 ∨ n=5) (e : (L ⧸ pCore 2 L) ≃* SL(n,ZMod 2)) : False := by
  have hg := h.raw_binary_linear_original_intersections_generate hG T hM hJ hu hZ hZne
    hSyl hL hq hf hn e
  have hs := ComponentModels.source20_sylow_intersection hL.2
  have hML := h.raw_binaryLinear_intersection_le_partner T hM.1.2 hu hfull hs hcubic (by omega) e
  apply hout
  refine le_inf hL.1 ?_
  rw [←hg]
  exact sup_le hML (inf_le_left.trans inf_le_right)

/-- A binary linear row of the actual normalizer B.5 image is impossible
at the original quintic source. The actual central core map supplies the
literal quotient marking; no star-image comparison is used. -/
theorem PreparedChosenModule.raw_not_binary_linear_normalizer_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hf : generalizedFitting L = pCore 2 L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc)
    (hcubic : (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤ centralizer (V : Set G))
    {n : ℕ} (hn : n=4 ∨ n=5)
    (e : let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
      let H := L ⊔ (S ⊓ normalizer (L : Set G))
      let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
      let q := QuotientGroup.mk' (centralizer (W : Set H))
      (L.subgroupOf H).map q ≃* SL(n,ZMod 2)) : False := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect hL.2
  have houtM : ¬L ≤ M := by
    intro hLM
    exact hout (le_inf hL.1 ((perfect_subgroup_centralizes_localModule hG T hempty hM hLM).trans
      (localModule_centralizer_le_partner T M hu)))
  obtain ⟨_,ec,_,_,_,hec,hker,_⟩ := h.raw_component_normalizer_quotient
    hG T hM hJ hu hZ hZne hL hq hf hout houtM
  let f := e.toMonoidHom.comp ec
  have hfs : Function.Surjective f := e.surjective.comp hec
  have hfk : f.ker ≤ center (L ⧸ pCore 2 L) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact hker
  let t := MulEquiv.ofBijective f (h.raw_local_binary_linear_cover_bijective hG T hZ hZne hL.1 hq hn f hfs hfk)
  exact h.raw_not_binary_linear_core hG T hM hJ hu hfull hZ hZne hSyl hL hq hf hout hcubic hn t

end CFSG.Quasithin.Chapter15.Section01
