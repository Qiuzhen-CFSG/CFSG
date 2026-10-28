module
public import Stellmacher.SectionEight.LocalQuotientHypotheses
public import Stellmacher.QuotientModuleIndexBound
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# Stellmacher (8.1)(a): equality of endpoint indices

Under Hypothesis 2 and a nontrivial commutator of the two critical endpoint
centers, their cross-core indices are equal. This is the first field of
Stellmacher (8.1), journal p.37, independently of the factor decomposition
in (1.7).

For each endpoint, construct its faithful centralizer quotient and apply
Section 1's relative module-measure bound to the opposite elementary center.
Critical minimality puts the final center in the distinguished Sylow S, so
(7.4) identifies its intersection with the initial centralizer as the initial
core intersection. At the other endpoint, choose a Sylow containing the
initial center and use (7.4)'s universal Sylow centralizer identity. The two
transported cardinal inequalities are opposite directions of the desired
equality. All local quotient action instances and their hypotheses are supplied
by the proved witness and local-hypotheses modules.
The local bound is also exported for the offender membership used by the
decomposition branch of (8.1).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

/-- The Section 1 index bound for a vertex center and a nontrivial elementary actor. -/
public theorem local_quotient_index_bound
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (d : Γ.Vertex)
    {l : Γ.Vertex} (hl : l ∈ neighborhood Γ d)
    (Y : Subgroup G) (hYP : Y ≤ stabilizer Γ d)
    [IsElementaryAbelian 2 Y]
    (hYnot : ¬ Y ≤ Subgroup.centralizer (z Γ d : Set G)) :
    Nat.card Y * Nat.card (z Γ d ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) ≤
      Nat.card (z Γ d) * Nat.card (Y ⊓ Subgroup.centralizer (z Γ d : Set G) : Subgroup G) := by
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hl
  have hzq : z Γ d ≤ q Γ d :=
    ((lemma_seven_three h Γ).center_core d l hl).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hqP : q Γ d ≤ stabilizer Γ d := by
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  obtain ⟨w⟩ := exists_quotientModuleWitness (stabilizer Γ d) (z Γ d)
    (hzq.trans hqP) (stabilizer_le_normalizer_z Γ d)
  exact w.index_bound Y hYP (local_quotient_hypotheses h Γ d hl w Y hYP hYnot)

/-- Stellmacher (8.1)(a): the critical endpoint indices are equal. -/
public theorem lemma_eight_one_index
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2) :
    QuotientCardEqual
      (ZAt ctx.Γ ctx.criticalPath.a)
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a' ⊓ QAt ctx.Γ ctx.criticalPath.a) := by
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have h74 := lemma_seven_four h Γ cp
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
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
  have hlast : last ∈ neighborhood Γ cp.a' :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hlast
  have hZendS : z Γ cp.a' ≤ S := by
    have hdist : Γ.distance cp.a' cp.firstStep < cp.length := by
      rw [Γ.distance_symm]
      have hd := SevenSix.path_distance_le Γ cp 1 cp.length (by omega) le_rfl
      have hd' : Γ.distance cp.firstStep cp.a' ≤ cp.length - 1 := by
        simpa [cp.path_first, cp.path_end] using hd
      omega
    exact (SevenSix.critical_minimality Γ cp hdist).trans
      (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hCfirst : z Γ cp.a' ⊓ Subgroup.centralizer (z Γ cp.a : Set G) =
      z Γ cp.a' ⊓ q Γ cp.a := by
    rw [← h74.edge_centralizer, ← inf_assoc, inf_eq_left.mpr hZendS]
  have hZaPend : z Γ cp.a ≤ stabilizer Γ cp.a' :=
    h74.first_containment.1.trans h74.first_containment.2
  let : IsElementaryAbelian 2 ((z Γ cp.a).subgroupOf (stabilizer Γ cp.a')) :=
    IsElementaryAbelian.subgroupOf hZaPend
  obtain ⟨T, hZaT⟩ :=
    (IsElementaryAbelian.isPGroup 2
      ((z Γ cp.a).subgroupOf (stabilizer Γ cp.a'))).exists_le_sylow
  have hZaW : z Γ cp.a ≤ sylowTwoAmbient (stabilizer Γ cp.a') T := by
    intro x hx
    exact ⟨⟨x, hZaPend hx⟩, hZaT hx, rfl⟩
  have hCend : z Γ cp.a ⊓ Subgroup.centralizer (z Γ cp.a' : Set G) =
      z Γ cp.a ⊓ q Γ cp.a' := by
    rw [← (h74.commutator_case ctx.commutator_ne).1 T,
      ← inf_assoc, inf_eq_left.mpr hZaW]
  have hZendnot : ¬ z Γ cp.a' ≤ Subgroup.centralizer (z Γ cp.a : Set G) := by
    intro hcentral
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hcentral
  have hZanot : ¬ z Γ cp.a ≤ Subgroup.centralizer (z Γ cp.a' : Set G) := by
    intro hcentral
    exact ctx.commutator_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral)
  have hle := local_quotient_index_bound h Γ cp.a hfirst (z Γ cp.a')
    h74.reverse_containment.1 hZendnot
  have hge := local_quotient_index_bound h Γ cp.a' hlast (z Γ cp.a) hZaPend hZanot
  rw [hCfirst, hCend] at hle hge
  exact le_antisymm hge hle

end Stellmacher.SectionEight
