module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwoPointOrdinary
public import Theory.GroupTheory.PResidual.PermutingPrimeLift
public import Theory.GroupTheory.Commutator.FixedSeedKernel

/-!
# An actual quintic actor for the point Sylow subgroup

Lift the order-five residual through the original module-centralizer
denominator using the prescribed point Sylow subgroup. Equality of quotient
images preserves every commutator on V. In particular, this same five-group
permutes with the actual C_T(a) and moves the original moving support fully.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- A quintic marked quotient supplies an actual five-group permuting with
the specified Sylow and retaining every displacement on the original module. -/
theorem caseI_exists_permuting_quintic_actor
    {M V Z S : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (hVM : V ≤ M) (hZ : Z ≤ V)
    (hSyl : Chapter1.IsSylowIn 2 S (M ⊓ centralizer (Z : Set G))) :
    let C := M ⊓ centralizer (Z : Set G)
    let N := M ⊓ centralizer (V : Set G)
    let R := (pResidual 2 C).map C.subtype
    letI := caseI_module_centralizer_normal (Z1 := Z) hn
    Nat.card (pResidual 2 (C ⧸ N.subgroupOf C)) = 5 →
    ∃ Y : Subgroup G, IsPGroup 5 Y ∧ IsPPerfect 2 Y ∧ Y ≤ R ∧
      (S : Set G) * (Y : Set G) = (Y : Set G) * (S : Set G) ∧
      (∀ D : Subgroup G, D ≤ V → ⁅D,Y⁆ = ⁅D,R⁆) ∧
      ⁅⁅V,R⁆,Y⁆ = ⁅V,R⁆ := by
  intro C N R hc
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : (N.subgroupOf C).Normal := caseI_module_centralizer_normal hn
  let q := QuotientGroup.mk' (N.subgroupOf C)
  obtain ⟨P, hP⟩ := hSyl
  obtain ⟨Y₀, hY, hperf, hperm, him, hYR⟩ :=
    exists_permuting_prime_residual_lift q (QuotientGroup.mk'_surjective _) P hc
  let Y := Y₀.map C.subtype
  have hVC : V ≤ C := le_inf hVM (V.le_centralizer.trans (centralizer_le hZ))
  have hker : q.ker ≤ centralizer (V.subgroupOf C : Set C) := by
    rw [QuotientGroup.ker_mk']
    intro x hx v hv
    exact Subtype.ext (hx.2 v hv)
  have heq : Y₀.map q = (pResidual 2 C).map q :=
    him.trans (map_pResidual_quotient 2 (N.subgroupOf C)).symm
  have hcomm (D : Subgroup G) (hDV : D ≤ V) : ⁅D,Y⁆ = ⁅D,R⁆ := by
    have he := congrArg (map C.subtype)
      (commutator_eq_of_centralizing_kernel (V.subgroupOf C) (D.subgroupOf C)
        Y₀ (pResidual 2 C) q hker (subgroupOf_mono C hDV) heq)
    simpa only [map_commutator, map_subgroupOf_eq_of_le (hDV.trans hVC)] using he
  refine ⟨Y, hY.map C.subtype,
    hperf.of_surjective (C.subtype.subgroupMap Y₀) (C.subtype.subgroupMap_surjective Y₀),
    map_mono hYR, ?_, hcomm, ?_⟩
  · have he := congrArg (Set.image C.subtype) hperm
    rw [Set.image_mul, Set.image_mul] at he
    change ((P : Subgroup C).map C.subtype : Set G) * (Y : Set G) =
      (Y : Set G) * ((P : Subgroup C).map C.subtype : Set G) at he
    rwa [hP] at he
  · obtain ⟨hWV, hmove⟩ := marked_residual_movement hn Z
    exact (hcomm _ hWV).trans hmove

end CFSG.Quasithin.Chapter15.Section01
