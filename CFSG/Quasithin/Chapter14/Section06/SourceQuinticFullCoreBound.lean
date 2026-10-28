module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticNinePath
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSecondKernelOrder
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiMinimalNinePath
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullCoreUpper

/-!
# Full original quintic core and kernel upper bounds

The original odd nine-path bounds the full Sylow by 4096. The genuine
Sz(2) quotient has order twenty and the Sylow has index five, giving the
full core bound 1024. The exact full second-kernel quotient of order
sixteen then bounds the literal kernel by 64. Both local Ree alternatives
remain possible; no universal order-512 bound is asserted.
-/

public noncomputable section
open Subgroup SimpleGraph Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
open Reduction CommutingNontrivial CommutingThreeProfile CommutingThreeProfile.ReducedLayer
variable {G : Type*} [Group G] [Finite G]

/-- The full original Sylow, core and centralizer kernel have upper orders
4096, 1024 and 64, retaining the full Ree alternative. -/
theorem source_quintic_full_core_and_kernel_upper
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    Nat.card (T : Subgroup G) ≤ 4096 ∧ Nat.card (pCore 2 H) ≤ 1024 ∧
      Nat.card C ≤ 64 := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := G₀ L (T : Subgroup G)
  let F := reducedFamily L (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨hF,_,hred,hB,hP,hJ,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change HypothesisF11 L (T : Subgroup G) at hF
  change SuzukiContainment.reducedSylow L (T : Subgroup G) = T at hred
  change B₀ L (T : Subgroup G) = T at hB
  change ∀ j, P₀ L (T : Subgroup G) j = L j at hP
  change J = H ⊔ X at hJ
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTJ : (T : Subgroup G) ≤ J := by rw [hJ]; exact hTH.trans le_sup_left
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple hF)
  have hstar : star L (T : Subgroup G) false = F false := by
    change (starredParabolic L (T : Subgroup G) 0).subgroupOf J =
      (P₀ L (T : Subgroup G) 0).subgroupOf J
    apply congrArg (fun K : Subgroup G => K.subgroupOf J)
    have hpar : parabolic L (T : Subgroup G) 0 = P₀ L (T : Subgroup G) 0 := by
      rw [P₀_eq_source hF,hred]
    exact le_antisymm ((starredParabolic_le 0).trans_eq hpar)
      ((hP 0).le.trans (local_le_starredParabolic 0))
  obtain ⟨Ry,hRy⟩ :=
    (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).2.2 false
  have hsyl : ∃ R : Sylow 2 (star L (T : Subgroup G) false),
      (R : Subgroup (star L (T : Subgroup G) false)).map
        (star L (T : Subgroup G) false).subtype = Q F (base F true) ⊔ Q F (base F false) := by
    rw [hstar]
    exact ⟨Ry,hRy.1.trans (sup_comm _ _)⟩
  obtain ⟨R,hR⟩ := hsyl
  obtain ⟨_,⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨_,⟨eX⟩⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  let eLin : (X ⧸ pCore 2 X) ≃* SL(2,ZMod 2) :=
    eX.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
  obtain ⟨ℓ,_,j,δ,_,_,_,K,_,_,_,_,_,v₀,p,hp,hm,hy,_⟩ :=
    small_suzuki_minimal_path_fixed_nine_path hF true eLin eSuz R hR
  have ho := (source_quintic_nine_path_odd hG T hempty hM hu hmany hcard e H hH hi
    p hp hm hy).1
  have hint : F false ⊓ F true = (T : Subgroup G).subgroupOf J := by
    have hh := (reduced_triple hF).intersection
    change F false ⊓ F true = (B₀ L (T : Subgroup G)).subgroupOf J at hh
    rwa [hB] at hh
  have hbase : IsPGroup 2 (F false ⊓ F true : Subgroup J) := by
    rw [hint]
    exact T.isPGroup'.comap_subtype
  let E := stabilizer F v₀ ⊓ stabilizer F (p.1 : Vertex F)
  obtain ⟨g,hg⟩ := edgeStabilizer_map_base F p.1.property
  have hE : E = (F false ⊓ F true).map (MulAut.conj g).toMonoidHom := hg
  have hEp : IsPGroup 2 E := hE ▸ hbase.map (MulAut.conj g).toMonoidHom
  have hval (v : Vertex F) : Nat.card ((graph F).neighborSet v) =
      if v.type = true then 3 else 5 := by
    simpa using source_linear_suzuki_neighbor_cards hF true eLin eSuz
      (by exact Nat.card_zmod 2) v
  have hbnd := two_subgroup_card_le_forwardCount_of_odd_fixer F
    (fun j => if j = true then 3 else 5) hval p hp E le_rfl hEp ho
  have hcount : BasedWalk.forwardCount (fun j => if j = true then 3 else 5)
      8 (p.1 : Vertex F).type = 4096 := by
    cases (p.1 : Vertex F).type <;> decide
  rw [hcount,hE,card_map_of_injective (MulAut.conj g).injective,hint,
    Nat.card_congr (subgroupOfEquivOfLe hTJ).toEquiv] at hbnd
  have hquot : Nat.card (H ⧸ pCore 2 H) = 20 :=
    (Nat.card_congr eSuz.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
  have hHcard := relIndex_mul_card_of_le hH.1.1.2
  rw [hi] at hHcard
  have hQcard := (pCore 2 H).card_mul_index
  rw [index_eq_card,hquot] at hQcard
  have hQupper : Nat.card (pCore 2 H) ≤ 1024 := by omega
  have hCQ : C ≤ H.pCoreIn 2 := source_quintic_span_centralizer_le_core hG T hM H hH hi
  obtain ⟨_,hN,_,hCquot,_⟩ := source_quintic_second_kernel_card_sixteen
    hG T hempty hM hu hmany hcard e H hH hi
  let := hN
  have hCcard := (C.subgroupOf (H.pCoreIn 2)).card_mul_index
  rw [index_eq_card] at hCcard
  change Nat.card (C.subgroupOf (H.pCoreIn 2)) *
    Nat.card (H.pCoreIn 2 ⧸ C.subgroupOf (H.pCoreIn 2)) = Nat.card (H.pCoreIn 2) at hCcard
  rw [hCquot,Nat.card_congr (subgroupOfEquivOfLe hCQ).toEquiv,
    show Nat.card (H.pCoreIn 2) = Nat.card (pCore 2 H) from
      card_map_of_injective H.subtype_injective] at hCcard
  change Nat.card (T : Subgroup G) ≤ 4096 ∧ Nat.card (pCore 2 H) ≤ 1024 ∧ Nat.card C ≤ 64
  exact ⟨hbnd,hQupper,by omega⟩

end CFSG.Quasithin.Chapter14.Section06
