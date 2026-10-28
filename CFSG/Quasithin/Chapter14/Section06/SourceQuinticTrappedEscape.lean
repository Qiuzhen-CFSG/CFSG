module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSFiveCentralizer
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticNeighborIntersectionLarge
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDihedralExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiRemoteFive
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiElementaryPathCard
public import Theory.GroupTheory.Commutator.AbelianCentralizerIndex

/-!
# Trapped centralizer escape in the original quintic graph

The binary local index identifies the trapped centralizer with its actual
incoming core intersection. If its remote intersection remained in the
next core, its intersection with the base span would centralize both
remote centers, hence an actual order-five subgroup of their join.
The original five-centralizer theorem and the original span-intersection
lower bound give a contradiction. All full cores remain literal.
-/

public noncomputable section
open Subgroup SimpleGraph Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
open CommutingNontrivial CommutingThreeProfile CommutingThreeProfile.ReducedLayer

private theorem small_suzuki_trapped_escape
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (Reduction.reducedFamily L S))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hq : Nat.card k = 2)
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) (!i)) ⊔
        Q (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) i))
    {a x z w c : Vertex (Reduction.reducedFamily L S)}
    (hxa : (graph (Reduction.reducedFamily L S)).Adj x a)
    (hxm : (graph (Reduction.reducedFamily L S)).Adj x (base (Reduction.reducedFamily L S) (!i)))
    (hyz : (graph (Reduction.reducedFamily L S)).Adj (base (Reduction.reducedFamily L S) i) z)
    (hwz : (graph (Reduction.reducedFamily L S)).Adj w z)
    (hwc : (graph (Reduction.reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (Reduction.reducedFamily L S) (!i))
    (hca : IsCriticalPair (Reduction.reducedFamily L S) a (base (Reduction.reducedFamily L S) i))
    (hcc : IsCriticalPair (Reduction.reducedFamily L S) c (base (Reduction.reducedFamily L S) i))
    (hRz : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (Reduction.reducedFamily L S) z ⊔ Q (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) i))
    (hZx : Nat.card (Z (Reduction.reducedFamily L S) x) = 2)
    (hZy : Nat.card (Z (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) i)) = 2)
    (hcommx : ⁅V (Reduction.reducedFamily L S) x 1,Q (Reduction.reducedFamily L S) x⁆ ≤
      Z (Reduction.reducedFamily L S) x)
    (hlarge : 4 < Nat.card (V (Reduction.reducedFamily L S) x 1 ⊓
      V (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) i) 1 :
      Subgroup (Reduction.G₀ L S)))
    (hfive : ∀ A : Subgroup (Reduction.G₀ L S), A ≤ star L S i → Nat.card A = 5 →
      V (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) i) 1 ⊓
        centralizer (A : Set (Reduction.G₀ L S)) ≤
          Z (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) i))
    (t : Reduction.G₀ L S) (ht : t ∈ Q (Reduction.reducedFamily L S) x)
    (htrap : V (Reduction.reducedFamily L S) x 1 ⊓ centralizer ({t} : Set (Reduction.G₀ L S)) ≤
      Q (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) i)) :
    let F := Reduction.reducedFamily L S
    let A := V F x 1 ⊓ centralizer ({t} : Set (Reduction.G₀ L S))
    A = V F x 1 ⊓ Q F (base F i) ∧ ¬ A ⊓ Q F w ≤ Q F c := by
  let F := Reduction.reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let X := V F x 1
  let Y := V F y 1
  let H := X ⊓ Y
  let A := X ⊓ centralizer ({t} : Set (Reduction.G₀ L S))
  let D := A ⊓ Q F w
  let E := Z F a ⊔ Z F c
  let : ∀ j, Finite (F j) := finite_endpoints (Reduction.reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1
  let := V_elementary F (Reduction.reduced_triple h).generate hZ (Reduction.reduced_kernel_sylow h) hb x
  let := V_elementary F (Reduction.reduced_triple h).generate hZ (Reduction.reduced_kernel_sylow h) hb y
  have hXm : X ≤ Q F m := V_le_neighbor_Q F (Reduction.reduced_triple h).generate hZ
    (Reduction.reduced_kernel_sylow h) hb hxm
  have hym : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hXy : X ≤ stabilizer F y := hXm.trans
    (((source_Z_Q_U (Reduction.reduced_triple h) m).2.trans (ballKernel_one_le_edge F hym.symm)).trans inf_le_right)
  have hYQ := V_le_Q F (Reduction.reduced_triple h).generate hZ (Reduction.reduced_kernel_sylow h) hb y
  let : Finite X := Finite.of_injective (inclusion hXy) (inclusion_injective _)
  let : Finite Y := Finite.of_injective (inclusion (hYQ.trans (Q_le_stabilizer F y))) (inclusion_injective _)
  let : Finite (Z F x) := Finite.of_injective (inclusion (Z_le_V F x 1)) (inclusion_injective _)
  let : Finite (Z F y) := Finite.of_injective (inclusion (Z_le_V F y 1)) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion (show H ≤ Y from inf_le_right)) (inclusion_injective _)
  have hXi : (Q F y).relIndex X = 2 := by
    have hu := source_small_suzuki_elementary_local_index h (!i) eLin
      (by cases i <;> exact eSuz) hq y X hXy
    change (Q F y).relIndex X ≤ 2 at hu
    have hn : (Q F y).relIndex X ≠ 1 := by
      intro he
      exact hca.2 (((Z_neighbor_le_V F hxa).trans (relIndex_eq_one.mp he)).trans
        (source_Z_Q_U (Reduction.reduced_triple h) y).2)
    have hp : (Q F y).relIndex X ≠ 0 := index_ne_zero_of_finite
    omega
  have hA : A = X ⊓ Q F y := abelian_singleton_centralizer_eq_intersection
    X (Q F x) (Z F x) (Q F y) (Z_le_V F x 1) hcommx ht (hXi.trans hZx.symm) htrap
  have hYz : Y ≤ Q F z := V_le_neighbor_Q F (Reduction.reduced_triple h).generate hZ
    (Reduction.reduced_kernel_sylow h) hb hyz
  have hYw : Y ≤ stabilizer F w := hYz.trans
    (((source_Z_Q_U (Reduction.reduced_triple h) z).2.trans (ballKernel_one_le_edge F hwz.symm)).trans inf_le_right)
  have hYi : (Q F w).relIndex Y ≤ 2 := source_small_suzuki_elementary_local_index h (!i) eLin
    (by cases i <;> exact eSuz) hq w Y hYw
  have haQ : Z F a ≤ Q F m := CommutingNontrivial.Z_le_Q_of_dist_lt_b F hZ a m
    (lt_of_le_of_lt ((graph F).dist_le (Walk.cons hxa.symm (Walk.cons hxm .nil))) hb)
    (Reduction.reduced_kernel_sylow h m)
  have hcQ : Z F c ≤ Q F z := CommutingNontrivial.Z_le_Q_of_dist_lt_b F hZ c z
    (lt_of_le_of_lt ((graph F).dist_le (Walk.cons hwc.symm (Walk.cons hwz .nil))) hb)
    (Reduction.reduced_kernel_sylow h z)
  have hEP : E ≤ star L S i := sup_le
    (haQ.trans ((le_sup_left.trans hT.ge).trans (map_subtype_le _)))
    (hcQ.trans ((le_sup_left.trans hRz.ge).trans (map_subtype_le _)))
  obtain ⟨B,hBE,hBc⟩ := source_small_suzuki_remote_centers_contain_five h i hb eSuz eLin hq
    hxa hxm hyz hwz hwc hzn hca hcc T R hT hRz
  refine ⟨hA,?_⟩
  intro hD
  have hHD : H ⊓ Q F w ≤ D := by
    intro u hu
    refine ⟨?_,hu.2⟩
    rw [hA]
    exact ⟨hu.1.1,hYQ hu.1.2⟩
  have hEC : H ⊓ Q F w ≤ centralizer (E : Set (Reduction.G₀ L S)) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · intro u hu v hv
      have huX : u ∈ X := Z_neighbor_le_V F hxa hu
      exact congrArg Subtype.val (mul_comm (⟨v,hv.1.1⟩ : X) ⟨u,huX⟩)
    · exact (Z_centralizes_Q F c (hZ c)).trans (centralizer_le (hHD.trans hD))
  have hHZ : H ⊓ Q F w ≤ Z F y :=
    (le_inf (inf_le_left.trans inf_le_right) (hEC.trans (centralizer_le hBE))).trans
      (hfive B (hBE.trans hEP) hBc)
  apply inf_not_le_of_card_gt_index_mul_card H Y (Q F w) (Z F y) inf_le_right hYi ?_ hHZ
  rw [show Nat.card (Z F y) = 2 from hZy]
  exact hlarge

variable {G : Type*} [Group G] [Finite G]

/-- The actual trapped centralizer on a critical six-edge segment equals
its incoming core intersection, whose remote intersection escapes the next
full core. Every cardinal and five-centralizer input comes from the original
quintic source. -/
theorem source_quintic_trapped_centralizer_escape
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let L : Fin 2 → Subgroup G := ![H,X]
    let F := Reduction.reducedFamily L (T : Subgroup G)
    ∀ {a x z w c : Vertex F},
      (graph F).Adj x a → (graph F).Adj x (base F true) → x ≠ base F false →
      (graph F).Adj (base F false) z → (graph F).Adj w z → (graph F).Adj w c →
      z ≠ base F true → IsCriticalPair F a (base F false) →
      IsCriticalPair F c (base F false) →
      ∀ t : Reduction.G₀ L (T : Subgroup G), t ∈ Q F x →
        V F x 1 ⊓ centralizer ({t} : Set (Reduction.G₀ L (T : Subgroup G))) ≤ Q F (base F false) →
        let A := V F x 1 ⊓ centralizer ({t} : Set (Reduction.G₀ L (T : Subgroup G)))
        A = V F x 1 ⊓ Q F (base F false) ∧ ¬ A ⊓ Q F w ≤ Q F c := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let y := base F false
  let m := base F true
  dsimp only
  intro a x z w c hxa hxm hxy hyz hwz hwc hzn hca hcc t ht htrap
  obtain ⟨hF,_,hred,_,hP,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change HypothesisF11 L (T : Subgroup G) at hF
  change SuzukiContainment.reducedSylow L (T : Subgroup G) = T at hred
  change ∀ j, Reduction.P₀ L (T : Subgroup G) j = L j at hP
  have hstar' (r : Fin 2) : starredParabolic L (T : Subgroup G) r =
      Reduction.P₀ L (T : Subgroup G) r := by
    have hpar : parabolic L (T : Subgroup G) r = Reduction.P₀ L (T : Subgroup G) r := by
      rw [Reduction.P₀_eq_source hF,hred]
    exact le_antisymm ((starredParabolic_le r).trans_eq hpar)
      ((hP r).le.trans (local_le_starredParabolic r))
  have hstar (j : Bool) : star L (T : Subgroup G) j = F j := by
    cases j
    · change (starredParabolic L (T : Subgroup G) 0).subgroupOf J =
        (Reduction.P₀ L (T : Subgroup G) 0).subgroupOf J
      exact congrArg (fun K : Subgroup G => K.subgroupOf J) (hstar' 0)
    · change (starredParabolic L (T : Subgroup G) 1).subgroupOf J =
        (Reduction.P₀ L (T : Subgroup G) 1).subgroupOf J
      exact congrArg (fun K : Subgroup G => K.subgroupOf J) (hstar' 1)
  obtain ⟨S₀,hS₀⟩ :=
    (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).2.2 false
  have hsyl : ∃ R : Sylow 2 (star L (T : Subgroup G) false),
      (R : Subgroup (star L (T : Subgroup G) false)).map
        (star L (T : Subgroup G) false).subtype = Q F m ⊔ Q F y := by
    rw [hstar false]
    exact ⟨S₀,hS₀.1.trans (sup_comm _ _)⟩
  obtain ⟨R,hR⟩ := hsyl
  obtain ⟨Rz,hRz⟩ := source_common_sylow_neighbors hF false R hR z hyz
  obtain ⟨_,⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨_,⟨eX⟩⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  let eLin : (X ⧸ pCore 2 X) ≃* SL(2,ZMod 2) :=
    eX.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
  have hb : 2 < b F := by
    have hh := (source_quintic_dgs_critical_three hG T hempty hM hu hmany hcard e H hH hi).1
    change b F = 3 at hh
    omega
  obtain ⟨hZymap,_⟩ := source_quintic_dgs_center_markings hG T hempty hM hu hmany hcard e H hH hi
  change (Z F y).map J.subtype = centralInvolutions T at hZymap
  have hZy : Nat.card (Z F y) = 2 := by
    rw [←card_map_of_injective J.subtype_injective,hZymap]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hcommy : ⁅V F y 1,Q F y⁆ = Z F y := by
    apply map_injective J.subtype_injective
    rw [map_commutator,
      (source_quintic_dgs_span_and_full_kernel hG T hempty hM hu hmany hcard e H hH hi).2.1,
      (hmaps false).2,hZymap]
    exact (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
  have hxtype : x.type = false := Bool.eq_false_iff.mpr hxm.1
  obtain ⟨g,hgx⟩ := Subgroup.CosetGeometry.exists_smul_base F x
  rw [hxtype] at hgx
  have hZx : Nat.card (Z F x) = 2 := by
    rw [←hgx,Z_translate,card_map_of_injective (MulAut.conj g).injective]
    exact hZy
  have hcommx : ⁅V F x 1,Q F x⁆ ≤ Z F x := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hcommy
    rw [map_commutator,←V_translate F,←Q_translate F,←Z_translate F,hgx] at hh
    exact hh.le
  have hlarge : 4 < Nat.card (V F x 1 ⊓ V F y 1 : Subgroup J) := by
    simpa only [inf_comm] using
      source_quintic_dgs_neighbor_intersection_large hG T hempty hM hu hmany hcard e H hH hi
        x hxm.symm hxy
  apply small_suzuki_trapped_escape hF false hb eSuz eLin (by simp only [Nat.card_zmod])
    R Rz hR hxa hxm hyz hwz hwc hzn hca hcc hRz hZx hZy hcommx hlarge ?_ t ht htrap
  intro B hB hBc
  exact (source_quintic_dgs_five_centralizer_base hG T hempty hM hu hmany hcard e H hH hi
    B (hB.trans_eq (hstar false)) hBc).1.le

end CFSG.Quasithin.Chapter14.Section06
