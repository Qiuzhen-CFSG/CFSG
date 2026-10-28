module
public import CFSG.Quasithin.Chapter15.Section01.ChosenNormalizerSource
public import Theory.GroupTheory.CubicCommutatorResidual
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# The residual splitting in the full Omega branch

Inside the literal N=N_M(C_T(V)), the chosen central seed gives reducedness
and O₂(N)=C_T(V); even characteristic gives a self-centralizing two-core.
The cubic residual splitting therefore applies with no extra core or
centralizer premise. The second theorem takes exactly X=O²([O²(N),P])
and the original commutator bound [C_T(V),P]≤V. Its remaining premises
are the actual Omega module's residual movement, fixed space and cubic image.

Source: Aschbacher–Smith15.1.11, final paragraph, printed p.1089.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_chosenNormalizer_cubicResidual_splitting
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) (hVne : V ≠ ⊥)
    (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M) :
    let N := chosenNormalizer T M V
    let W := V.subgroupOf N
    letI : W.Normal := (chosenNormalizer_reduced T hTM hVM hMV hspan).normal
    ∀ X : Subgroup N, W ≤ X → IsPPerfect 2 X → ⁅pCore 2 N,X⁆ ≤ W →
      W ⊓ centralizer (X : Set N) = ⊥ →
      IsElementaryAbelian 3 (X.map (QuotientGroup.mk' (centralizer (W : Set N)))) →
      X.map N.subtype ⊓ centralizer (V : Set G) = V ∧
        (T : Subgroup G) ⊓ centralizer (V : Set G) =
          V ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓
            centralizer (X.map N.subtype : Set G)) ∧
        Disjoint V ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓
          centralizer (X.map N.subtype : Set G)) := by
  dsimp only
  let N := chosenNormalizer T M V
  let W := V.subgroupOf N
  have hred := chosenNormalizer_reduced T hTM hVM hMV hspan
  let : W.Normal := hred.normal
  let : IsElementaryAbelian 2 W := hred.elementary
  intro X hWX hX hcomm hfixed himage
  have hN := Chapter1.mem_He_iff.mp (chosenNormalizer_mem_He hG T hTM hVM hVne hMV)
  obtain ⟨hk,hs,hd⟩ := cubic_residual_core_splitting W X hred.le_pCore hWX
    hred.le_centralizer_pCore hN hX hcomm hfixed himage
  have hWN : V ≤ N := module_le_chosenNormalizer T hTM hVM hMV
  have hWmap : W.map N.subtype = V := map_subgroupOf_eq_of_le hWN
  have hRmap : (pCore 2 N).map N.subtype =
      (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    chosenNormalizer_twoCore T hTM hVM hMV hspan
  have hCmap : (pCore 2 N ⊓ centralizer (X : Set N)).map N.subtype =
      (T : Subgroup G) ⊓ centralizer (V : Set G) ⊓
        centralizer (X.map N.subtype : Set G) := by
    rw [map_inf _ _ _ N.subtype_injective,map_centralizer_subtype,
      ←inf_assoc,inf_eq_left.mpr (map_subtype_le _),hRmap]
  refine ⟨?_,?_,?_⟩
  · have he := congrArg (map N.subtype) hk
    rwa [map_inf _ _ _ N.subtype_injective,map_centralizer_subtype,
      ←inf_assoc,inf_eq_left.mpr (map_subtype_le _),hWmap] at he
  · have he := congrArg (map N.subtype) hs
    rwa [Subgroup.map_sup,hWmap,hCmap,hRmap] at he
  · have he := disjoint_map N.subtype_injective hd
    rwa [hWmap,hCmap] at he


/-- The literal source residual splits C_T(V) and P centralizes the fixed factor. -/
theorem source_chosenNormalizer_commutatorResidual_splitting
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) (hVne : V ≠ ⊥)
    (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M) :
    let N := chosenNormalizer T M V
    let W := V.subgroupOf N
    letI : W.Normal := (chosenNormalizer_reduced T hTM hVM hMV hspan).normal
    ∀ P : Subgroup N,
      let X := cubicCommutatorResidual P
      ⁅pCore 2 N,P⁆ ≤ W → ⁅W,X⁆ = W →
      W ⊓ centralizer (X : Set N) = ⊥ →
      IsElementaryAbelian 3 (X.map (QuotientGroup.mk' (centralizer (W : Set N)))) →
      X.map N.subtype ⊓ centralizer (V : Set G) = V ∧
        (T : Subgroup G) ⊓ centralizer (V : Set G) =
          V ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓
            centralizer (X.map N.subtype : Set G)) ∧
        Disjoint V ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓
          centralizer (X.map N.subtype : Set G)) ∧
        P.map N.subtype ≤ centralizer ((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓
          centralizer (X.map N.subtype : Set G) : Set G) := by
  dsimp only
  let N := chosenNormalizer T M V
  let W := V.subgroupOf N
  have hred := chosenNormalizer_reduced T hTM hVM hMV hspan
  let : W.Normal := hred.normal
  intro P hcomm hmove hfixed himage
  let X := cubicCommutatorResidual P
  obtain ⟨hk,hs,hd⟩ := source_chosenNormalizer_cubicResidual_splitting hG T hTM hVM hVne
    hMV hspan X (le_cubicCommutatorResidual_of_moved P W hmove)
    (isPPerfect_embedded_pResidual 2 _) (cubicCommutatorResidual_two_layer P _ W hcomm)
    hfixed himage
  refine ⟨hk,hs,hd,?_⟩
  have hc : P ≤ centralizer (pCore 2 N ⊓ centralizer (X : Set N) : Set N) :=
    centralizes_core_fixed_of_normalizes_residual W X P _ le_normalizer_of_normal
      (le_sup_right.trans (cubicCommutatorResidual_normalized P)) hcomm hfixed
  have he : (pCore 2 N ⊓ centralizer (X : Set N)).map N.subtype =
      (T : Subgroup G) ⊓ centralizer (V : Set G) ⊓
        centralizer (X.map N.subtype : Set G) := by
    rw [map_inf _ _ _ N.subtype_injective,map_centralizer_subtype,
      ←inf_assoc,inf_eq_left.mpr (map_subtype_le _)]
    exact congrArg (fun R : Subgroup G => R ⊓ centralizer (X.map N.subtype : Set G))
      (chosenNormalizer_twoCore T hTM hVM hMV hspan)
  change P.map N.subtype ≤ centralizer
    (((T : Subgroup G) ⊓ centralizer (V : Set G) ⊓
      centralizer (X.map N.subtype : Set G) : Subgroup G) : Set G)
  rw [←he]
  exact (map_mono hc).trans (map_centralizer_le_centralizer_image _ _)
end CFSG.Quasithin.Chapter15.Section01
