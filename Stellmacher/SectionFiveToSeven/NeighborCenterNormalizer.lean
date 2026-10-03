module

public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# A neighboring center is not normalized by the opposite stabilizer

Under the Section Seven hypotheses, the center subgroup at one endpoint of
an edge cannot be normalized by the other endpoint stabilizer. Otherwise both
stabilizers normalize it, and adjacent stabilizers generate the graph group.
The center subgroup is a two-group by (7.3) and is nontrivial because it contains
the omega-center of an edge Sylow. It would therefore lie in the graph group's
trivial two-core.

This common argument supports the geometric center exclusion in (9.3) and
the nontrivial extracted-center action in the first step of (9.10). Source:
Stellmacher, Journal of Algebra 190 (1997), printed pp.49 and 57, together
with (7.3). The public interface uses only Section Seven graph data.
-/

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext SevenSix

universe u

private theorem omega_center_nontrivial
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (hS : IsPGroup 2 S) (hne : S ≠ ⊥) :
    omegaOneCenter S ≠ ⊥ := by
  let _ : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hne
  let _ : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  obtain ⟨n, hn, hcard⟩ :=
    (hS.to_subgroup (Subgroup.center S)).nontrivial_iff_card.mp inferInstance
  have hdiv : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot (G := S) (Subgroup.center S) 2 hdiv
  intro hbot
  apply hinner
  apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
  simpa [omegaOneCenter] using hbot

public theorem neighbor_center_not_normalized
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    (d l : Γ.Vertex) (hl : l ∈ neighborhood Γ d) :
    ¬ stabilizer Γ d ≤ Subgroup.normalizer (z Γ l : Set G) := by
  let T : Sylow 2 ↥(stabilizer Γ d ⊓ stabilizer Γ l) := default
  let W := sylowTwoAmbient (stabilizer Γ d ⊓ stabilizer Γ l) T
  obtain ⟨hthree,_,hL,_,hgen,hZn⟩ := edge_sectionThree_data h Γ hl T
  have hOmega : omegaOneCenter W ≤ z Γ l := by
    obtain ⟨U,hU⟩ := hL.1.2.1
    rw [z, Γ.zAt_def]
    exact le_sSup ⟨U, congrArg omegaOneCenter hU.symm⟩
  have hZne : z Γ l ≠ ⊥ := by
    intro hbot
    exact omega_center_nontrivial W hthree.nontrivial_two_subgroup.2
      hthree.nontrivial_two_subgroup.1 (bot_unique (hOmega.trans_eq hbot))
  have hreverse : d ∈ neighborhood Γ l :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hl))
  have hZp : IsPGroup 2 (z Γ l) :=
    (z_isElementaryAbelian_of_neighbor h Γ hreverse).isPGroup
  intro hdn
  have hGlN : stabilizer Γ l ≤ Subgroup.normalizer (z Γ l : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZn.1).mp hZn.2
  have htopN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (z Γ l : Set G) := by
    rw [← hgen]
    exact sup_le hdn hGlN
  have hnormal : (z Γ l).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_unique htopN)
  have hcore : z Γ l ≤ pCore 2 G := le_sSup ⟨hnormal,hZp⟩
  exact hZne (bot_unique (hcore.trans_eq h.twoCore_eq_bot))


end Stellmacher.SectionsFiveToSeven
