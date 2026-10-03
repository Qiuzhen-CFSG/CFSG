module

public import Stellmacher.LaterDefs
public import Stellmacher.SectionEight.EightFiveFirstStepFixedLine
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven

/-!
# The two adjacent centers in the long-path argument of (8.5)

For a noncommuting critical pair of length greater than two, assume that
the first-step center is central in its stabilizer, the initial center has
order four, and the initial two-core quotient is SL₂(2). The commutator of
the endpoint centers equals both the first-step and penultimate centers.
This is the center-identification input to the separate distance argument.

The imported fixed-line theorem uses the actual faithful quotient action
from (8.1), its projected Sylow, and the nontrivial barred offender join.
Orbit parity and faithfulness give an order-two fixed subgroup, and the
Sylow omega-center transfers it to the first-step center inside the initial
center. No identification with the ambient LocalJ is made.

Edge transitivity carries the initial edge to the terminal edge. The wrong
orientation would make the terminal center central in its own stabilizer,
contradicting endpoint noncommutation and (7.4). The correct orientation
transports order four, the fixed-line containment, and centrality to the
opposite end. Critical minimality puts each endpoint center in the other
adjacent stabilizer. Quadratic action and Lagrange then identify the
nontrivial commutator with both order-two fixed lines.

Source: Stellmacher, Journal of Algebra 190 (1997), journal p.40, the final
paragraph of (8.5), `refs/files/stellmacher-n-group.pdf`. Neither (8.5) nor
its distance conclusion is used, and no reversed normalized path is assumed.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem four_fixed_line
    {G : Type u} [Group G] [Finite G]
    (moduleGroup actor line : Subgroup G)
    (hfour : Nat.card moduleGroup = 4)
    (htwo : Nat.card line = 2)
    (hline : line ≤ moduleGroup ⊓ Subgroup.centralizer (actor : Set G))
    (hcomm : ⁅moduleGroup, actor⁆ ≠ ⊥)
    (hbound : ⁅moduleGroup, actor⁆ ≤ moduleGroup)
    (hquadratic : ⁅⁅moduleGroup, actor⁆, actor⁆ = ⊥) :
    ⁅moduleGroup, actor⁆ = line := by
  let fixed := moduleGroup ⊓ Subgroup.centralizer (actor : Set G)
  have hproper : fixed ≠ moduleGroup := by
    intro heq
    apply hcomm
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact heq ▸ (inf_le_right : fixed ≤ Subgroup.centralizer (actor : Set G))
  have hlt : Nat.card fixed < 4 := by
    have hle := Subgroup.card_le_of_le (inf_le_left : fixed ≤ moduleGroup)
    rw [hfour] at hle
    apply lt_of_le_of_ne hle
    intro heq
    exact hproper (Subgroup.eq_of_le_of_card_ge inf_le_left (hfour.trans heq.symm).le)
  have hdiv : Nat.card fixed ∣ 4 := by
    rw [← hfour]
    exact Subgroup.card_dvd_of_le (inf_le_left : fixed ≤ moduleGroup)
  have hfixed : Nat.card fixed = 2 := by
    have hle := Subgroup.card_le_of_le hline
    rw [htwo] at hle
    change 2 ≤ Nat.card fixed at hle
    have hsmall : Nat.card fixed = 2 ∨ Nat.card fixed = 3 := by omega
    rcases hsmall with hsmall | hsmall
    · exact hsmall
    · norm_num [hsmall] at hdiv
  have hlineEq : line = fixed :=
    Subgroup.eq_of_le_of_card_ge hline (by omega)
  have hcommLe : ⁅moduleGroup, actor⁆ ≤ fixed :=
    le_inf hbound (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hquadratic)
  have hcommTwo : Nat.card (⁅moduleGroup, actor⁆ : Subgroup G) = 2 := by
    have hle := Subgroup.card_le_of_le hcommLe
    have hpos := Nat.card_pos (α := (⁅moduleGroup, actor⁆ : Subgroup G))
    have hne : Nat.card (⁅moduleGroup, actor⁆ : Subgroup G) ≠ 1 := by
      intro hone
      exact hcomm (Subgroup.card_eq_one.mp hone)
    omega
  exact (Subgroup.eq_of_le_of_card_ge hcommLe (by omega)).trans hlineEq.symm

private theorem vertex_commutator_act
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (actor : G) (vertex : Γ.Vertex)
    (hcentral : ⁅z Γ vertex, stabilizer Γ vertex⁆ = ⊥) :
    ⁅z Γ (Γ.act actor vertex), stabilizer Γ (Γ.act actor vertex)⁆ = ⊥ := by
  rw [z_act, stabilizer_act, conjugateBy, ← Subgroup.map_commutator,
    hcentral, Subgroup.map_bot]

/-- In the long-path case of (8.5), the endpoint commutator is both adjacent
centers, with the original centrality, cardinality, and quotient hypotheses. -/
public theorem eight_five_critical_centers_of_card_four_and_quotient
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hquotient : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlong : 2 < ctx.criticalPath.length) :
    let last := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩
    ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
        ZAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
        ZAt ctx.Γ last := by
  have hlocal := eight_five_first_step_fixed_line_of_card_four_and_quotient
    ctx hcenter hfour hquotient hlong
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 2 < cp.length := hlong
  let h7 := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let last := cp.path ⟨cp.length - 1, by omega⟩
  have h74 := lemma_seven_four h7 Γ cp
  have hlastadj : Γ.adjacent cp.a' last := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self cp.length⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hi, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  have hfirstcentral : ⁅z Γ cp.firstStep, stabilizer Γ cp.firstStep⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcenter.trans (SevenSix.centerAmbient_le_centralizer _))
  obtain ⟨actor, horientation⟩ :=
    (lemma_seven_one h7 Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hlastadj
  have halignment : Γ.act actor cp.a = cp.a' ∧
      Γ.act actor cp.firstStep = last := by
    rcases horientation with halignment | hswapped
    · exact halignment
    · exfalso
      have hendcentral := vertex_commutator_act Γ actor cp.firstStep hfirstcentral
      rw [hswapped.2] at hendcentral
      apply ctx.commutator_ne
      rw [Subgroup.commutator_comm]
      apply bot_unique
      exact (Subgroup.commutator_mono le_rfl
        (h74.first_containment.1.trans h74.first_containment.2)).trans hendcentral.le
  have hlastcentral : ⁅z Γ last, stabilizer Γ last⁆ = ⊥ := by
    have htransport := vertex_commutator_act Γ actor cp.firstStep hfirstcentral
    rwa [halignment.2] at htransport
  have hendfour : Nat.card (z Γ cp.a') = 4 := by
    rw [← halignment.1, z_act, Subgroup.card_map_of_injective
      (MulAut.conj actor⁻¹).injective]
    exact hfour
  have hlasttwo : Nat.card (z Γ last) = 2 := by
    rw [← halignment.2, z_act, Subgroup.card_map_of_injective
      (MulAut.conj actor⁻¹).injective]
    exact hlocal.1
  have hlastle : z Γ last ≤ z Γ cp.a' := by
    rw [← halignment.1, ← halignment.2, z_act, z_act]
    exact Subgroup.map_mono hlocal.2
  have hendfirst : z Γ cp.a' ≤ stabilizer Γ cp.firstStep := by
    have hdist : Γ.distance cp.a' cp.firstStep < cp.length := by
      rw [Γ.distance_symm]
      have hbound := SevenSix.path_distance_le Γ cp 1 cp.length (by omega) le_rfl
      have hbound' : Γ.distance cp.firstStep cp.a' ≤ cp.length - 1 := by
        simpa [cp.path_first, cp.path_end] using hbound
      omega
    exact (SevenSix.critical_minimality Γ cp hdist).trans (by
      rw [q, Γ.twoCoreAt_def]
      exact Subgroup.map_subtype_le _)
  have hastartlast : z Γ cp.a ≤ stabilizer Γ last := by
    have hdist : Γ.distance cp.a last < cp.length := by
      have hbound := SevenSix.path_distance_le Γ cp 0 (cp.length - 1) (by omega) (by omega)
      have hbound' : Γ.distance cp.a last ≤ cp.length - 1 := by
        simpa [last, cp.path_start] using hbound
      omega
    exact (SevenSix.critical_minimality Γ cp hdist).trans (by
      rw [q, Γ.twoCoreAt_def]
      exact Subgroup.map_subtype_le _)
  have hRinitial : ⁅z Γ cp.a, z Γ cp.a'⁆ ≤ z Γ cp.a :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (h74.reverse_containment.1.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hRterminal : ⁅z Γ cp.a', z Γ cp.a⁆ ≤ z Γ cp.a' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((h74.first_containment.1.trans h74.first_containment.2).trans
        (stabilizer_le_normalizer_z Γ cp.a'))
  constructor
  · apply four_fixed_line (z Γ cp.a) (z Γ cp.a') (z Γ cp.firstStep)
      hfour hlocal.1 _ ctx.commutator_ne hRinitial h74.quadratic.2
    exact le_inf hlocal.2
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hfirstcentral).trans
        (Subgroup.centralizer_le hendfirst))
  · rw [Subgroup.commutator_comm]
    apply four_fixed_line (z Γ cp.a') (z Γ cp.a) (z Γ last)
      hendfour hlasttwo _ _ hRterminal h74.quadratic.1
    · exact le_inf hlastle
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hlastcentral).trans
          (Subgroup.centralizer_le hastartlast))
    · simpa only [Subgroup.commutator_comm] using ctx.commutator_ne

end Stellmacher.SectionEight
