module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveCentralizer
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSFullKernel

/-!
# The original five-centralizer in the marked quintic graph

The order-five centralizer calculation is transported through the actual
completion inclusion.  We keep the full graph second kernel: the result is an
equality with the centralizer of the graph's full second kernel, rather than a
premature identification with its central line.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]

theorem source_quintic_dgs_five_centralizer_base
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (A : Subgroup (Reduction.G₀ ![H, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G)))
    (hA : A ≤ Reduction.reducedFamily ![H, sourceResidual M Mc ⊔ (T : Subgroup G)]
      (T : Subgroup G) false) (hAc : Nat.card A = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let J := Reduction.G₀ ![H,X] (T : Subgroup G)
    let F := Reduction.reducedFamily ![H,X] (T : Subgroup G)
    let y := base F false
    V F y 1 ⊓ centralizer (A : Set J) = Z F y ∧
      Q F y ⊓ centralizer (A : Set J) =
        ballKernel F y 2 ⊓ centralizer (A : Set J) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let y := base F false
  have hF := source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨_,_,_,_,_,_,hmaps,_⟩ := hF
  have hHmap : (F false).map J.subtype = H := (hmaps false).1
  have hQmap : (Q F y).map J.subtype = H.pCoreIn 2 := (hmaps false).2
  obtain ⟨hspan, hcore⟩ :=
    source_quintic_dgs_span_and_full_kernel hG T hempty hM hu hmany hcard e H hH hi |>.2
  change (V F y 1).map J.subtype = conjugateSpanBy (localModule T M) H at hspan
  change (ballKernel F y 2).map J.subtype =
    H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) at hcore
  have hAmap : A.map J.subtype ≤ H := by
    rw [← hHmap]
    exact map_mono hA
  have hAcard : Nat.card (A.map J.subtype) = 5 := by
    rw [card_map_of_injective J.subtype_injective]
    exact hAc
  obtain ⟨hU,hQ⟩ := source_quintic_five_centralizers
    hG T hempty hM hu hmany hcard e H hH hi (A.map J.subtype) hAmap hAcard
  have hU' : (conjugateSpanBy (localModule T M) H) ⊓
      centralizer (A.map J.subtype : Set G) = centralInvolutions T := hU
  have hQ' : H.pCoreIn 2 ⊓ centralizer (A.map J.subtype : Set G) =
      (H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G)) ⊓
        centralizer (A.map J.subtype : Set G) := hQ
  constructor
  · apply map_injective J.subtype_injective
    rw [← map_inf_centralizer_of_injective J.subtype J.subtype_injective]
    rw [hspan]
    rw [hU']
    rw [show (Z F y).map J.subtype = centralInvolutions T by
      exact (source_quintic_dgs_center_markings hG T hempty hM hu hmany hcard e H hH hi).1]
  · apply map_injective J.subtype_injective
    rw [← map_inf_centralizer_of_injective J.subtype J.subtype_injective]
    rw [← map_inf_centralizer_of_injective J.subtype J.subtype_injective]
    rw [hQmap,hcore]
    exact hQ'

end CFSG.Quasithin.Chapter14.Section06
