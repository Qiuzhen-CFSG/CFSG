module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticElementarySecondKernel
public import Theory.GroupAction.RankTwoCosetGeometry.SecondBallKernel

/-!
# Bounding original elementary subgroups normalized by the cubic endpoint

The actual completion inclusion transports an elementary subgroup from the
two original cores. Normalization by the full cubic endpoint puts it in
the full second ball, where the original nine-path bound applies.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]

/-- The elementary normal subgroups in both original cores have order at most 32. -/
theorem source_quintic_elementary_normal_core_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : E ≤ H.pCoreIn 2 ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2)
    (hn : sourceResidual M Mc ⊔ (T : Subgroup G) ≤ normalizer (E : Set G)) :
    Nat.card E ≤ 32 := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  obtain ⟨_,_,_,_,_,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  have hXmap : (F true).map J.subtype = X := (hmaps true).1
  have hXJ : X ≤ J := hXmap ▸ map_subtype_le (F true)
  have hEJ : E ≤ J := (hE.trans inf_le_right).trans ((pCoreIn_le 2 X).trans hXJ)
  let E₀ := E.subgroupOf J
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.subgroupOf hEJ
  have hE₀map : E₀.map J.subtype = E := map_subgroupOf_eq_of_le hEJ
  have hE₀Q : E₀ ≤ Q F (base F false) ⊓ Q F (base F true) := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hE₀map,map_inf _ _ _ J.subtype_injective,(hmaps false).2,(hmaps true).2]
    exact hE
  have hE₀F : E₀ ≤ F true := by
    have hh := (hE₀Q.trans inf_le_right).trans (Q_le_stabilizer F (base F true))
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using hh
  have hn₀ : F true ≤ normalizer (E₀ : Set J) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro z
    have hxX : (x : G) ∈ X := hXmap ▸ mem_map_of_mem J.subtype hx
    exact mem_normalizer_iff.mp (hn hxX) (z : G)
  let : (E₀.subgroupOf (F true)).Normal := normal_subgroupOf_of_le_normalizer hn₀
  have hfirst := (source_quintic_dgs_span_and_full_kernel
    hG T hempty hM hu hmany hcard e H hH hi).1
  have hnormal : E₀.subgroupOf (F true) ≤
      ((ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1).subgroupOf
        (F true)).normalCore := by
    apply normal_le_normalCore.mpr
    rw [(hfirst false).1,(hfirst true).1]
    exact subgroupOf_mono _ hE₀Q
  rw [←base_ballKernel_two F true] at hnormal
  have hE₂ : E₀ ≤ ballKernel F (base F true) 2 := by
    intro x hx
    exact hnormal (show (⟨x,hE₀F hx⟩ : F true) ∈ E₀.subgroupOf (F true) from hx)
  have hbound := source_quintic_elementary_second_kernel_card
    hG T hempty hM hu hmany hcard e H hH hi E₀ inferInstance hE₂
  have hc : Nat.card E₀ = Nat.card E := Nat.card_congr (subgroupOfEquivOfLe hEJ).toEquiv
  exact hc ▸ hbound

end CFSG.Quasithin.Chapter14.Section06
