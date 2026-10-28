module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenFirstCoreIntersection
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCartan
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceLocalKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedTerminal
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightHalfActor

/-!
# The whole binary core fixed by the original Cartan

The full Cartan lies in the binary local permutation kernel. Its centralizer
in the entire binary two-core propagates into the adjacent eight-field core.
The actual first-core intersection identifies this fixed subgroup with the
original binary center plane. No selected path or action comparison is used.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCartanFixedCore
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile CommutingOneProfile CommutingNontrivial

private theorem core_cartan_fixed_le_neighbor {G : Type*} [Group G]
    {L : Fin 2→Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S))
    (hpar : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (eβ : (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true))) ≃* SL(2,k))
    (hCker : (cartan c).map (bOne_tree_map h)≤U (reducedFamily L S) (base (reducedFamily L S) false))
    (hCne : (cartan c).map (bOne_tree_map h)≠⊥)
    (hkk : U (reducedFamily L S) (base (reducedFamily L S) false)⊓
      U (reducedFamily L S) (base (reducedFamily L S) true)=
        Q (reducedFamily L S) (base (reducedFamily L S) false)⊓
          Q (reducedFamily L S) (base (reducedFamily L S) true)) :
    Q (reducedFamily L S) (base (reducedFamily L S) false)⊓
      centralizer ((cartan c).map (bOne_tree_map h):Set (G₀ L S))≤
        Q (reducedFamily L S) (base (reducedFamily L S) true) := by
  let A := reducedAmalgam L S
  let UP := Universal.cosetFamily A
  let F := reducedFamily L S
  let φ := bOne_tree_map h
  let C := (cartan c).map φ
  let α := base F false
  let β := base F true
  let E := F false⊓F true
  let W := (twoGroup L S).map φ
  let V := Q F α⊓centralizer (C:Set (G₀ L S))
  let _ : ∀ i,Finite (F i) := finite_endpoints (reduced_triple h)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hmapE : (originalMiddle A).map φ=E := by
    rw [show originalMiddle A=UP false⊓UP true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact (bOne_tree_cover h).map_inf
  have hC0 : C≤E := hmapE ▸ map_mono (cartan_le c)
  have hW0 : W≤E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hWn : E≤normalizer (W:Set (G₀ L S)) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hWcore : W≤E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hW0 hWn
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite E := Finite.of_injective (inclusion (show E≤F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hd : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨r,hr⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hg : C⊔E.pCoreIn 2=E := by
    apply le_antisymm (sup_le hC0 (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    exact he.symm.le.trans (sup_le (hWcore.trans le_sup_right) le_sup_left)
  have hEbase : E=stabilizer F α⊓stabilizer F β := by
    rw [show stabilizer F α=F false from Subgroup.CosetGeometry.stabilizer_base F false,
      show stabilizer F β=F true from Subgroup.CosetGeometry.stabilizer_base F true]
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hs : sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S))=7 :=
    (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2.unique hpar.2
  have hCV : C≤centralizer (V:Set (G₀ L S)) := le_centralizer_iff.mp inf_le_right
  exact CommutingTrivial.cartan_kernel_centralizer_le_neighbor_core
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hab
    (sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) α (by omega))
    eβ C V C (hEbase ▸ hC0) (hEbase ▸ hd) (hEbase ▸ hg) inf_le_left
    (hCV.trans (Subgroup.centralizer_le_normalizer _)) le_rfl hCker ho hCne hCV hkk

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
local notation "Fₛ" => reducedFamily Lₛ Sₛ

set_option maxHeartbeats 800000 in
/-- The entire original binary core fixed by the prescribed whole Cartan
is exactly its original binary center plane. -/
theorem source_binary_core_cartan_fixed
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) :
    let h : HypothesisF11 Lₛ Sₛ := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
    let C := (cartan c).map (bOne_tree_map h)
    Q Fₛ (base Fₛ false)⊓centralizer (C:Set (G₀ Lₛ Sₛ))=Z Fₛ (base Fₛ false) := by
  let h : HypothesisF11 Lₛ Sₛ := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  let ι := (G₀ Lₛ Sₛ).subtype
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let α := base Fₛ false
  let β := base Fₛ true
  have hCmap : C.map ι=c.D 0⊔c.D 1 := by
    rw [Subgroup.map_map]
    exact SourceEightHalfActor.original_cartan_image hG T hempty hM hu hmany hcard e H hH eR c
  have hC7 : Nat.card C=7 := by
    rw [←card_map_of_injective (G₀ Lₛ Sₛ).subtype_injective,hCmap]
    have hh := SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c
    rw [cartan,card_map_of_injective middleMap_injective,
      Nat.card_congr (subgroupOfEquivOfLe c.joint_le).toEquiv] at hh
    exact hh
  have hCne : C≠⊥ := by intro he; rw [he,Subgroup.card_bot] at hC7; omega
  have hCker : C≤U Fₛ α := by
    change C≤ballKernel Fₛ α 1
    have hh := (map_mono (SourceBinaryCartan.source_binary_cartan_kernel
      hG T hempty hM hu hmany hcard e H hH eR c)).trans
        (cov.ballKernel_map_le (base (Universal.cosetFamily (reducedAmalgam Lₛ Sₛ)) false) 1)
    simpa only [cov.vertex_base] using hh
  let eβ : (graphLocalGroup Fₛ β ⧸ pCore 2 (graphLocalGroup Fₛ β)) ≃* SL(2,GaloisField 2 3) :=
    (reduced_graphLinearQuotient h true (residualQuotientEquiv H eR)).trans
      (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (GaloisField 2 3)).symm
  have hab : (graph Fₛ).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hle := core_cartan_fixed_le_neighbor h c
    (source_path_profile hG T hempty hM hu hmany hcard e H hH eR).1 eβ hCker hCne
    (SourceLocalKernels.source_adjacent_kernel_intersection hG T hempty hM hu hmany hcard e H hH eR hab)
  have hfirst := SourceSevenFirstCoreIntersection.source_seven_first_core_intersection
    hG T hempty hM hu hmany hcard e H hH eR c
  change (Q Fₛ β⊓centralizer (C:Set (G₀ Lₛ Sₛ)))⊓Q Fₛ α=Z Fₛ α at hfirst
  apply le_antisymm
  · intro x hx
    exact hfirst.le ⟨⟨hle hx,hx.2⟩,hx.1⟩
  · intro x hx
    have hh := hfirst.ge hx
    exact ⟨hh.2,hh.1.2⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCartanFixedCore
