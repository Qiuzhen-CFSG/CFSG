module
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
/-!
# Sylow spans for an action with at most two conjugates

If an acting subgroup has at most two conjugates of R, each of its Sylow
2-subgroups generates the full conjugate span of R. In the nontrivial
case the stabilizer has index two, so the odd Sylow index supplies an
element outside it. The index-two coset calculation gives the same two
conjugates. R need not lie in the acting subgroup.

Source: the Sylow-orbit step of Aschbacher–Smith 5.2.2, printed p.648,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow two-subgroup sees the entire conjugate span when the acting
subgroup has at most two conjugates of the given subgroup. -/
theorem conjugateSpanBy_sylow_eq_of_relIndex_le_two
    (R N : Subgroup G) (T : Sylow 2 N)
    (hi : (normalizer (R : Set G)).relIndex N ≤ 2) :
    conjugateSpanBy R ((T : Subgroup N).map N.subtype) = conjugateSpanBy R N := by
  let J := normalizer (R : Set G)
  change J.relIndex N ≤ 2 at hi
  have hpos : 0 < J.relIndex N := Nat.pos_of_ne_zero (J.subgroupOf N).index_ne_zero_of_finite
  have he : J.relIndex N = 1 ∨ J.relIndex N = 2 := by omega
  rcases he with he | he
  · have hNR : N ≤ J := relIndex_eq_one.mp he
    exact le_antisymm (conjugateSpanBy_mono le_rfl (map_subtype_le _))
      ((conjugateSpanBy_le le_rfl hNR).trans (le_conjugateSpanBy _ _))
  · have hn : ¬ (T : Subgroup N) ≤ J.subgroupOf N := by
      intro ht
      have hd := index_dvd_of_le ht
      change J.relIndex N ∣ T.index at hd
      rw [he] at hd
      exact T.not_dvd_index hd
    obtain ⟨t,ht,hnt⟩ := Set.not_subset.mp hn
    have htN : (t : G) ∈ N := t.property
    have htT : (t : G) ∈ (T : Subgroup N).map N.subtype := mem_map_of_mem _ ht
    have ho := componentOrbit_eq_sup_of_index_two R N J he inf_le_right htN hnt
    have hspan : conjugateSpanBy R N = componentOrbit R N := conjugateSpanBy_eq_iSup_conj R N
    apply le_antisymm (conjugateSpanBy_mono le_rfl (map_subtype_le _))
    rw [hspan,ho]
    apply sup_le (le_conjugateSpanBy _ _)
    rintro x ⟨r,hr,rfl⟩
    exact subset_closure ⟨t,htT,r,hr,rfl⟩
end Subgroup
