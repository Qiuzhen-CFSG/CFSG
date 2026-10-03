module
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.CriticalPairNormalization
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts

/-!
# Noncentrality and noncommutation for shifted critical pairs in (8.2)

In the noncentral first-step case of the exact local Section Eight context,
every vertex center is noncentral in its stabilizer, and every critical pair
has a nontrivial endpoint-center commutator. These facts justify retaining
the Section Eight hypotheses when the proof of (8.2) shifts a critical pair
and normalizes it back to the distinguished edge.

The given nonzero endpoint commutator makes the initial vertex center
noncentral, using (7.4)'s reverse containment. Every vertex lies on an edge;
edge transitivity carries it to one end of the distinguished edge. Covariance
of stabilizers and vertex centers transports centrality, contradicting either
initial noncentrality or the given first-step hypothesis. For an arbitrary
critical pair, the existing normalization theorem gives an anchored critical
path. If its endpoint centers commuted, (7.5) would identify its terminal
center with the stabilizer's omega-center, contradicting noncentrality.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), printed pp.37–38,
the opening noncentrality assertion and the repeated shifted critical pairs,
in `refs/latex/stellmacher-n-group.tex`. Neither backward noncontainment nor
the critical-distance-one conclusion is assumed or reproved here. The same
graph and critical-path definitions are retained without additional fields.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem central_of_commutator_bot
    {G : Type*} [Group G] (A B : Subgroup G) (hle : A ≤ B)
    (hcomm : ⁅A, B⁆ = ⊥) : A ≤ CenterAmbient B := by
  intro element helement
  refine ⟨⟨element, hle helement⟩, ?_, rfl⟩
  change (⟨element, hle helement⟩ : B) ∈ Subgroup.center B
  rw [Subgroup.mem_center_iff]
  intro other
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm helement)
    other other.property)

private theorem central_act
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (actor : G) (vertex : Γ.Vertex)
    (hcentral : z Γ vertex ≤ CenterAmbient (stabilizer Γ vertex)) :
    z Γ (Γ.act actor vertex) ≤ CenterAmbient (stabilizer Γ (Γ.act actor vertex)) := by
  apply central_of_commutator_bot
  · rw [z_act, stabilizer_act]
    exact Subgroup.map_mono (hcentral.trans (Subgroup.map_subtype_le _))
  · rw [z_act, stabilizer_act]
    change ⁅(z Γ vertex).map (MulAut.conj actor⁻¹).toMonoidHom,
      (stabilizer Γ vertex).map (MulAut.conj actor⁻¹).toMonoidHom⁆ = ⊥
    rw [← Subgroup.map_commutator]
    have hcomm : ⁅z Γ vertex, stabilizer Γ vertex⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcentral.trans (SevenSix.centerAmbient_le_centralizer _))
    rw [hcomm, Subgroup.map_bot]

private theorem exists_neighbor
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (vertex : Γ.Vertex) :
    ∃ neighbor, Γ.adjacent vertex neighbor := by
  obtain ⟨actor, hvertex | hvertex⟩ := Γ.coset₁_surjective vertex
  all_goals
    have hedge : Γ.adjacent (Γ.coset₁ actor) (Γ.coset₂ actor) := by
      rw [Γ.adj_cosets]
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨actor, Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩,
        Set.mem_smul_set.mpr ⟨1, P2.one_mem, by simp⟩⟩
  · exact ⟨Γ.coset₂ actor, hvertex ▸ hedge⟩
  · exact ⟨Γ.coset₁ actor, hvertex ▸ Γ.adjacent_symm hedge⟩

public theorem eight_two_all_vertex_centers_noncentral_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ∀ vertex : ctx.Γ.Vertex,
      ¬ ZAt ctx.Γ vertex ≤ CenterAmbient (GAt ctx.Γ vertex) := by
  have hstart : ¬ z ctx.Γ ctx.criticalPath.a ≤
      CenterAmbient (stabilizer ctx.Γ ctx.criticalPath.a) := by
    intro hcentral
    apply ctx.commutator_ne
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcentral.trans ((SevenSix.centerAmbient_le_centralizer _).trans
        (Subgroup.centralizer_le
          (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).reverse_containment.1)))
  intro vertex hcentral
  obtain ⟨neighbor, hadj⟩ := exists_neighbor ctx.Γ vertex
  obtain ⟨actor, hedge | hedge⟩ :=
    (lemma_seven_one ctx.sectionSeven ctx.Γ).edge_not_vertex_transitive.1
      hadj ctx.criticalPath.firstStep_adj
  · exact hstart (by simpa only [hedge.1] using central_act ctx.Γ actor vertex hcentral)
  · exact hcenter (by simpa only [hedge.1] using central_act ctx.Γ actor vertex hcentral)

public theorem eight_two_critical_pair_commutator_ne_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (left right : ctx.Γ.Vertex) (hcritical : IsCriticalPair ctx.Γ left right) :
    ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ ≠ ⊥ := by
  intro hcomm
  obtain ⟨actor, cp, hleft, hright, _hlength⟩ :=
    exists_criticalPath_of_critical_pair ctx.sectionSeven ctx.Γ ctx.criticalPath
      left right hcritical
  have hcomm' : ⁅z ctx.Γ cp.a, z ctx.Γ cp.a'⁆ = ⊥ := by
    rw [hleft, hright, z_act, z_act, ← Subgroup.map_commutator]
    rw [show ⁅z ctx.Γ left, z ctx.Γ right⁆ = ⊥ from hcomm, Subgroup.map_bot]
  apply eight_two_all_vertex_centers_noncentral_local ctx hcenter cp.a'
  change z ctx.Γ cp.a' ≤ _
  rw [lemma_seven_five_endpoint_center ctx.sectionSeven ctx.Γ cp hcomm']
  exact SevenSix.omegaOneCenter_le_centerAmbient _

end Stellmacher.SectionEight
