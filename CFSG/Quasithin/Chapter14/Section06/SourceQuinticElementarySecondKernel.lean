module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticNinePath
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiMinimalNinePath
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiElementaryPathCard

/-!
# The original elementary second-kernel bound

The original source constructs a normalized nonbacktracking nine-path.
Its full pointwise stabilizer has odd order, so the five remaining binary
local actions bound every elementary subgroup of the cubic second kernel
by thirty-two. No path, oddness, or cardinal bound is supplied as an input.
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

/-- The full cubic second kernel has no elementary subgroup of order above 32. -/
theorem source_quintic_elementary_second_kernel_card
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
    let J := G₀ L (T : Subgroup G)
    let F := reducedFamily L (T : Subgroup G)
    ∀ E : Subgroup J, IsElementaryAbelian 2 E →
      E ≤ ballKernel F (base F true) 2 → Nat.card E ≤ 32 := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := G₀ L (T : Subgroup G)
  let F := reducedFamily L (T : Subgroup G)
  dsimp only
  intro E hEA hE
  let := hEA
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
  have hcommon (j : Bool) : ∃ R : Sylow 2 (star L (T : Subgroup G) j),
      (R : Subgroup (star L (T : Subgroup G) j)).map
        (star L (T : Subgroup G) j).subtype = Q F (base F (!j)) ⊔ Q F (base F j) := by
    obtain ⟨R,hR⟩ :=
      (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).2.2 j
    rw [hstar j]
    refine ⟨R,?_⟩
    cases j
    · exact hR.1.trans (sup_comm _ _)
    · exact hR.1
  obtain ⟨Tlin,hTlin⟩ := hcommon true
  obtain ⟨Ry,hRy⟩ := hcommon false
  obtain ⟨_,⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨_,⟨eX⟩⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  let eLin : (X ⧸ pCore 2 X) ≃* SL(2,ZMod 2) :=
    eX.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
  have hfield : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  obtain ⟨ℓ,_,j,δ,_,_,_,C,_,_,_,_,_,v₀,p,hp,hm,hy,_⟩ :=
    small_suzuki_minimal_path_fixed_nine_path hF true eLin eSuz Ry hRy
  have ho := (source_quintic_nine_path_odd hG T hempty hM hu hmany hcard e H hH hi
    p hp hm hy).1
  have hEp : E ≤ ballKernel F (p.2.1 : Vertex F) 2 := by
    simpa only [hm] using hE
  exact source_small_suzuki_elementary_second_kernel_card_on_path
    hF true eLin eSuz hfield p ho E hEp

end CFSG.Quasithin.Chapter14.Section06
