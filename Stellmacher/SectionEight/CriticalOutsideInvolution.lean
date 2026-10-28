module
public import Stellmacher.LaterDefs
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven

/-!
# A critical involution outside the initial local core

The noncommuting critical-pair hypotheses supply an involution of the initial
stabilizer outside its two-core. Reversed criticality in (7.4) places an
element of the final center outside the initial core, while the containment
in (7.4)(b) places it in the initial stabilizer. The final center is elementary
abelian by the neighbor-center facts, so this element has square one.

This retains a crucial graph-derived input for the terminal classification
in Stellmacher (8.2), Journal of Algebra 190 (1997), p.38: the weaker local
core and quotient data alone also admit A4:C4, which has no involution outside
its two-core. No assertion about all vertices or critical distance one is
assumed here.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem critical_initial_has_involution_outside_core
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2) :
    ∃ t : GAt ctx.Γ ctx.criticalPath.a,
      t ∉ pCore 2 (GAt ctx.Γ ctx.criticalPath.a) ∧ t ^ 2 = 1 := by
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have h74 := lemma_seven_four h Γ cp
  have hlen := cp.length_pos
  let last : Γ.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have he := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hi, cp.path_end] at he
    exact Γ.adjacent_symm he
  have hlast := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hlast
  have hnot := (h74.commutator_case ctx.commutator_ne).2.2
  obtain ⟨t, htZ, htQ⟩ := SetLike.not_le_iff_exists.mp hnot
  let tP : stabilizer Γ cp.a := ⟨t, h74.reverse_containment.1 htZ⟩
  refine ⟨tP, ?_, ?_⟩
  · intro ht
    apply htQ
    change t ∈ Γ.twoCoreAt cp.a
    rw [Γ.twoCoreAt_def]
    exact Subgroup.mem_map_of_mem (stabilizer Γ cp.a).subtype ht
  · apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (A := z Γ cp.a') t htZ

end Stellmacher.SectionEight
