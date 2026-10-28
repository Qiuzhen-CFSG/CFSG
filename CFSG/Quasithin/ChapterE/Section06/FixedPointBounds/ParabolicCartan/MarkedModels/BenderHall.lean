module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Construction
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Cyclic
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.BenderHall.Reduction
public import Theory.SpecificGroups.BenderBorelCyclicQuotient
public import Theory.GroupTheory.Hall.NormalTwoCore

/-!
# Hall control in the single Bender branch

The actual component/Borel marking supplies a cyclic quotient by the
Borel's two-core for PSL₂, Suzuki and PSU₃. The source center identity
lifts this to an abelian quotient of M ∩ K by its own two-core, through
the distinct quotients X/O₂(X) and X/J. Component normality comes from
the source product and subnormal perfectness. Hall conjugacy then supplies
the original-Sylow normalizer factorization. Applying the existing cyclic
torus construction completes the intrinsic Hall--Cartan consumer.

Source: Aschbacher--Smith, E.2.2(2a), printed pp.215--216;
E.6.27, p.257; and the Borel/Frattini argument in 4.4.13, pp.623--624.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open BenderHall ChapterB
universe u v
variable {X : Type u} [Group X] [Finite X]

private theorem overlap_core_quotient_of_marked_borel {M K T : Subgroup X}
    (hc : SingleClauses M K T) (hO : pCore 2 X ≤ sourceKernel M)
    {A : Type v} [Group A] {B : Subgroup A} (hB : ModelBorelPair M K B)
    (hcyc : IsCyclic (B ⧸ pCore 2 B)) :
    IsMulCommutative ((M ⊓ K : Subgroup X) ⧸ pCore 2 (M ⊓ K : Subgroup X)) := by
  obtain ⟨q, hq, hqk, r, hr, hrk⟩ := BenderHall.SingleClauses.central_borel_lift hc hO hB
  let : Finite B := Finite.of_surjective r hr
  let := hcyc
  exact commutative_core_quotient_of_two_stage (p := 2) q hq hqk r hr hrk

/-- The actual Bender marking, with its central extension retained, gives
an abelian quotient of the original component overlap by its two-core. -/
theorem bender_overlap_core_quotient (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X} {f : ℕ}
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hm : BenderModel (minimalParabolicMax S hP) K f) :
    IsMulCommutative ((minimalParabolicMax S hP ⊓ K : Subgroup X) ⧸
      pCore 2 (minimalParabolicMax S hP ⊓ K : Subgroup X)) := by
  have hO := twoCore_le_sourceKernel S hP
  rcases hm with (hlin | hsuz) | huni
  · obtain ⟨F, hfield, hfin, hchar, _, hcard, hB⟩ := hlin
    let := hfield
    let := hfin
    let := hchar
    exact overlap_core_quotient_of_marked_borel hc hO hB
      (Theory.SpecificGroups.BenderBorel.psl2_borel_cyclic_quotient hcard)
  · obtain ⟨m, hm, _, hB⟩ := hsuz
    exact overlap_core_quotient_of_marked_borel hc hO hB
      (Theory.SpecificGroups.BenderBorel.suzuki_borel_cyclic_quotient m (by omega))
  · obtain ⟨F, hfield, hfin, hchar, J, hJ, _, _, _, _, hB⟩ := huni
    let := hfield
    let := hfin
    let := hchar
    exact overlap_core_quotient_of_marked_borel hc hO hB
      (Theory.SpecificGroups.BenderBorel.unitary_borel_cyclic_quotient J hJ)

private theorem hallControl_of_overlap_core_quotient (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hK : K.IsCComponent) (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hcomm : IsMulCommutative ((minimalParabolicMax S hP ⊓ K : Subgroup X) ⧸
      pCore 2 (minimalParabolicMax S hP ⊓ K : Subgroup X))) : HallControl S hP := by
  let M := minimalParabolicMax S hP
  let N := (M ⊓ K).subgroupOf M
  let : N.Normal := BenderHall.SingleClauses.overlap_normal hc hK
  let e : N ≃* (M ⊓ K : Subgroup X) := subgroupOfEquivOfLe inf_le_left
  let eq := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
    (IsPGroup.ker_isPGroup_of_injective e.injective)
  let : IsMulCommutative (N ⧸ pCore 2 N) := by
    refine ⟨⟨fun a b => eq.injective ?_⟩⟩
    simp only [map_mul]
    exact hcomm.is_comm.comm _ _
  have hSM : (S : Subgroup X) ≤ M := (minimalParabolicMax_spec S hP).2
  let SM := S.subtype hSM
  have hsup : N ⊔ (SM : Subgroup M) = ⊤ := by
    apply top_unique
    intro x _
    have hprod : (M : Set X) = (M ⊓ K : Subgroup X) * (S : Set X) :=
      BenderHall.SingleClauses.maximal_product hc hSM
    have hxmem : (x : X) ∈ (M : Set X) := x.property
    rw [hprod] at hxmem
    obtain ⟨k, hk, s, hs, he⟩ := Set.mem_mul.mp hxmem
    have hx : (⟨k, hk.1⟩ : M) * ⟨s, hSM hs⟩ = x := Subtype.ext he
    rw [← hx]
    exact mul_mem (mem_sup_left hk) (mem_sup_right hs)
  have hN : IsPGroup 2 (M ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (SM : Subgroup M) SM.isPGroup' hsup
  obtain ⟨hsolv, hcontrol⟩ := hall_control_from_normal_core_quotient N hN SM
  have hout (Y : Subgroup X) (hYM : Y ≤ M)
      (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf M)) :
      IsMulCommutative Y ∧ ∃ Q : Subgroup X, Y ≤ normalizer (Q : Set X) ∧
        (S : Set X) = (Q : Set X) *
          ((S : Subgroup X) ⊓ normalizer (Y : Set X) : Set X) := by
    obtain ⟨hYcomm, Q, hYQ, hfac⟩ := hcontrol (Y.subgroupOf M) hHall
    have hcommY : IsMulCommutative Y := by
      let j := (subgroupOfEquivOfLe hYM).symm
      refine ⟨⟨fun a b => j.injective ?_⟩⟩
      simp only [map_mul]
      exact hYcomm.is_comm.comm _ _
    let QX := Q.map M.subtype
    have hYQX : Y ≤ normalizer (QX : Set X) := by
      have hh := (map_mono (f := M.subtype) hYQ).trans (Q.le_normalizer_map M.subtype)
      simpa only [map_subgroupOf_eq_of_le hYM] using hh
    have hnormalizer : ((SM : Subgroup M) ⊓ normalizer (Y.subgroupOf M : Set M)).map
        M.subtype = (S : Subgroup X) ⊓ normalizer (Y : Set X) := by
      change ((SM : Subgroup M) ⊓ normalizer (Y.comap M.subtype : Set M)).map M.subtype = _
      rw [← comap_normalizer_eq_of_le_range (f := M.subtype)
        (show Y ≤ M.subtype.range from by simpa only [range_subtype] using hYM)]
      change (((S : Subgroup X) ⊓ normalizer (Y : Set X)).subgroupOf M).map
        M.subtype = _
      exact map_subgroupOf_eq_of_le (inf_le_left.trans hSM)
    have hi := congrArg (Set.image M.subtype) hfac
    rw [Set.image_mul] at hi
    change (((S : Subgroup X).subgroupOf M).map M.subtype : Set X) =
      (QX : Set X) *
        (((SM : Subgroup M) ⊓ normalizer (Y.subgroupOf M : Set M)).map M.subtype : Set X) at hi
    rw [map_subgroupOf_eq_of_le hSM, hnormalizer] at hi
    exact ⟨hcommY, QX, hYQX, hi⟩
  exact ⟨hsolv, fun Y hYM hHall => (hout Y hYM hHall).1,
    fun Y hYM hHall => (hout Y hYM hHall).2⟩

/-- Hall control for all three single Bender families, preserving the actual
central extension and the original Sylow subgroup. -/
theorem bender_hallControl (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {K : Subgroup X} {f : ℕ} (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hm : BenderModel (minimalParabolicMax S hP) K f) : HallControl S hP :=
  hallControl_of_overlap_core_quotient S hP hK hc (bender_overlap_core_quotient S hP hc hm)

/-- The single Bender branch supplies the intrinsic Hall--Cartan data from
its marked model, including the exact cyclic subgroup of order 2ⁿ(X) - 1. -/
theorem bender_intrinsic (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hn : 1 < generationParameter X) {K : Subgroup X} (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hm : BenderModel (minimalParabolicMax S hP) K (generationParameter X)) :
    Nonempty (IntrinsicHallCartanData S hP (generationParameter X)) :=
  intrinsic_of_cyclic_and_hallControl S hP (by omega)
    (bender_hallControl S hP hK hc hm) hm.cyclic

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
