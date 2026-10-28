module

public import Theory.GroupTheory.CComponent.Radical
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SylowCommutingJoin
/-!
# Sylow intersections and the radical of a C-component

A full ambient Sylow subgroup intersects a finite commuting join of
subnormal subgroups in the join of its intersections with the factors.
An actual Sylow two-subgroup of a C-component cannot centralize the component
modulo the ambient solvable radical when the simple radical quotient has
even order: its image would be a trivial Sylow subgroup of an even group.

Source application: Aschbacher--Smith, Proposition A.3.12, first assertion,
printed pp.47--48. The even-order premise is explicit; no odd-order theorem
or trivial-two-core assumption on the local ambient group is used here.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A full ambient Sylow intersects a commuting join in the join of its exact factor intersections. -/
theorem sylow_inf_iSup_of_commuting_subnormal {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    {ι : Type*} [Finite ι] (L : ι → Subgroup G)
    (hn : ∀ i, (L i).IsSubnormal)
    (hc : Pairwise fun i j => ∀ x y : G, x ∈ L i → y ∈ L j → Commute x y) :
    (T : Subgroup G) ⊓ (⨆ i, L i) = ⨆ i, (T : Subgroup G) ⊓ L i := by
  classical
  let H := ⨆ i, L i
  let U := ⨆ i, (T : Subgroup G) ⊓ L i
  have hUT : U ≤ (T : Subgroup G) := iSup_le fun _ => inf_le_left
  have hUH : U ≤ H := iSup_le fun i => inf_le_right.trans (le_iSup L i)
  choose S hS using fun i => T.exists_subgroupOf_eq_of_subnormal (L i) (hn i)
  obtain ⟨P, hP⟩ := exists_sylow_iSup_le_of_commuting L hc S U (by
    intro i
    rw [hS i, subgroupOf_map_subtype]
    exact le_iSup (fun i => (T : Subgroup G) ⊓ L i) i)
  have hPT : (P : Subgroup H) ≤ (T : Subgroup G).subgroupOf H :=
    map_le_iff_le_comap.mp (hP.trans hUT)
  have he : (P : Subgroup H) = (T : Subgroup G).subgroupOf H :=
    (P.is_maximal' (T.isPGroup'.comap_subtype) hPT).symm
  apply le_antisymm
  · change (P : Subgroup H).map H.subtype ≤ U at hP
    rw [he, subgroupOf_map_subtype] at hP
    exact hP
  · exact le_inf hUT hUH

/-- An actual Sylow two-subgroup acts nontrivially modulo the radical of the local ambient group. -/
theorem IsCComponent.not_sylow_commutator_le_solvableRadical {B : Subgroup G} (hB : B.IsCComponent)
    (heven : Even (Nat.card (B ⧸ solvableRadical B))) (S : Sylow 2 B) :
    ¬ ⁅B, (S : Subgroup B).map B.subtype⁆ ≤ solvableRadical G := by
  intro hcomm
  let Q := B ⧸ solvableRadical B
  let := hB.isSimpleGroup_quotient_solvableRadical
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (hB.not_isMulCommutative_quotient_solvableRadical
        (center_eq_top_iff.mp hz)).elim
  have hr : (solvableRadical G).subgroupOf B ≤ solvableRadical B := by
    apply le_solvableRadical _ inferInstance
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap (solvableRadical G))
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x : solvableRadical G => (x : G)) hab)))
  have hi : ⁅(⊤ : Subgroup B), (S : Subgroup B)⁆ ≤ solvableRadical B := by
    apply le_trans _ hr
    apply map_le_iff_le_comap.mp
    simpa only [map_commutator, ← MonoidHom.range_eq_map, range_subtype] using hcomm
  let q := QuotientGroup.mk' (solvableRadical B)
  let P := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hc : ⁅(⊤ : Subgroup Q), (P : Subgroup Q)⁆ = ⊥ := by
    have hm : ⁅(⊤ : Subgroup B), (S : Subgroup B)⁆.map q = ⊥ := by
      rw [map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hi
    simpa only [P, Sylow.coe_mapSurjective, map_commutator,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using hm
  have hPc : (P : Subgroup Q) ≤ center Q := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact ((commutator_eq_bot_iff_le_centralizer.mp hc (mem_top y)) x hx).symm
  have hpbot : (P : Subgroup Q) = ⊥ := le_bot_iff.mp (hPc.trans_eq hz)
  apply P.not_dvd_index
  rw [hpbot, index_bot]
  exact even_iff_two_dvd.mp heven
end Subgroup
