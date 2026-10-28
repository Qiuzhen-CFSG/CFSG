module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Construction
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.Hall.TwoClosedNormal

/-!
# Reduction of diagram Hall control to the covered component Borel

The single-component source product X = KS, subnormality and perfectness
identify K with O²(X). Thus K is normal, as is its overlap with M inside M,
and the quotient of M by that overlap is a two-group.

The remaining concrete assertion is that this original overlap is two-closed
with abelian odd quotient. From it, Hall subgroups lie in the overlap and
embed in its abelian quotient. The normal-core Frattini argument in
`Theory.GroupTheory.Hall.TwoClosedNormal` supplies the required factorization
on the original Sylow subgroup. This reduction does not identify X/J with
X/O₂(X), and does not assert the missing central-cover Borel calculation.

Source: Aschbacher--Smith, E.2.2(2), pp.215--216; 4.4.13, pp.623--624.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall
open ChapterB
variable {X : Type*} [Group X] [Finite X]

/-- The source product and C-component axioms identify the component with O²(X). -/
theorem single_component_eq_twoResidual (S : Sylow 2 X) {M K : Subgroup X}
    (hK : K.IsCComponent) (hc : SingleClauses M K S) : pResidual 2 X = K := by
  let := hK.perfect
  have hp : IsPPerfect 2 K := by
    intro N hN hp
    let := hN
    have hs : Subsingleton (K ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  apply pResidual_eq_of_subnormal_product K S hK.subnormal hp S.isPGroup'
  intro x
  exact Set.mem_mul.mp (hc.product ▸ Set.mem_univ x)

/-- Component normality is proved from the source product; it is not assumed. -/
theorem single_component_normal (S : Sylow 2 X) {M K : Subgroup X}
    (hK : K.IsCComponent) (hc : SingleClauses M K S) : K.Normal := by
  rw [← single_component_eq_twoResidual S hK hc]
  infer_instance

omit [Finite X] in
/-- The overlap is normal inside M and its quotient is a two-group. -/
theorem single_overlap_quotient_two (S : Sylow 2 X) {M K : Subgroup X}
    (hSM : (S : Subgroup X) ≤ M) (hc : SingleClauses M K S) [K.Normal] :
    IsPGroup 2 (M ⧸ K.subgroupOf M) := by
  apply isPGroup_quotient_of_sup_eq_top (K.subgroupOf M) (S.subtype hSM)
    (S.subtype hSM).isPGroup'
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨k, hk, s, hs, he⟩ := Set.mem_mul.mp (hc.product ▸ Set.mem_univ x.val)
  have hkM : k ∈ M := by
    have hh := M.mul_mem x.property (M.inv_mem (hSM hs))
    simpa only [← he, mul_inv_cancel_right] using hh
  have he' : (⟨k, hkM⟩ : M) * ⟨s, hSM hs⟩ = x := Subtype.ext he
  rw [← he']
  exact mul_mem (mem_sup_left hk) (mem_sup_right hs)

/-- The remaining model assertion concerns the actual covered component overlap. -/
abbrev CoveredBorelControl (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) : Prop :=
  OddHall.TwoClosedAbelianQuotient (K.subgroupOf (minimalParabolicMax S hP))

/-- The covered Borel calculation supplies all three Hall-control conclusions.
The quotient and Sylow subgroup are transported through the actual inclusion in X. -/
theorem hallControl_of_coveredBorel (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X} (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hb : CoveredBorelControl S hP K) : HallControl S hP := by
  let M := minimalParabolicMax S hP
  have hSM : (S : Subgroup X) ≤ M := (minimalParabolicMax_spec S hP).2
  let : K.Normal := single_component_normal S hK hc
  have hq := single_overlap_quotient_two S hSM hc
  have hsolv : Group.IsSolvable M := hb.solvable_extension hq
  have hyB (Y : Subgroup X) (hYM : Y ≤ M)
      (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf M)) :
      Y.subgroupOf M ≤ K.subgroupOf M :=
    OddHall.odd_subgroup_le _ _ hq (OddHall.odd_hall_odd hHall)
  refine ⟨hsolv, ?_, ?_⟩
  · intro Y hYM hHall
    change Y ≤ M at hYM
    change IsHallSubgroup oddPrimes (Y.subgroupOf M) at hHall
    let := hb.odd_subgroup_abelian (hyB Y hYM hHall) (OddHall.odd_hall_odd hHall)
    let e := subgroupOfEquivOfLe hYM
    apply IsMulCommutative.of_comm
    intro a b
    apply e.symm.injective
    simp only [map_mul]
    exact mul_comm' _ _
  · intro Y hYM hHall
    change Y ≤ M at hYM
    change IsHallSubgroup oddPrimes (Y.subgroupOf M) at hHall
    have hy := hyB Y hYM hHall
    obtain ⟨Q, hYQ, hf⟩ := OddHall.normal_twoClosed_frattini
      (K.subgroupOf M) hb (S.subtype hSM) (Y.subgroupOf M) hy (hHall.subgroupOf hy)
    refine ⟨Q.map M.subtype, ?_, ?_⟩
    · have hh := (map_mono (f := M.subtype) hYQ).trans (le_normalizer_map M.subtype)
      simpa only [map_subgroupOf_eq_of_le hYM] using hh
    · have hh := congrArg (Set.image M.subtype) hf
      rw [Set.image_mul] at hh
      have hS : (M.subtype '' (S.subtype hSM : Set M)) = (S : Set X) := by
        change (((S : Subgroup X).subgroupOf M).map M.subtype : Set X) = _
        rw [map_subgroupOf_eq_of_le hSM]
        rfl
      have hN : M.subtype ''
          (((S.subtype hSM : Subgroup M) ⊓ normalizer (Y.subgroupOf M : Set M)) : Set M) =
          (((S : Subgroup X) ⊓ normalizer (Y : Set X)) : Set X) := by
        change (((S.subtype hSM : Subgroup M) ⊓ normalizer (Y.subgroupOf M : Set M)).map
          M.subtype : Set X) = _
        rw [← subgroupOf_normalizer_eq hYM]
        change (((((S : Subgroup X) ⊓ normalizer (Y : Set X)).subgroupOf M).map
          M.subtype) : Set X) = _
        rw [map_subgroupOf_eq_of_le (inf_le_left.trans hSM)]
        rfl
      rw [hS, hN] at hh
      exact hh

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall
