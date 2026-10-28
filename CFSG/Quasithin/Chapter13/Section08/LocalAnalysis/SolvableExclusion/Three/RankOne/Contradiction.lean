module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.RankOne.ActorBounds
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.RankOne.EndpointActions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.RankOne.Geometry

/-!
# The cyclic and contained three-primary contradictions

The faithful actor bounds force |Uγ*|=|Vγ*|=2. Corrected 13.8.10 gives
both rank-one quotients. The solvable 13.8.5 transvection exclusion, transported
to the actual endpoint, then forces V₁≤Uγ. Irreducibility on the Frattini
quotient proves normal generation at both ends. Source 13.8.9 noncentrality
and 13.8.11(1) now force Uγ*<Vγ*, contradicting their equal orders.

This is an alternative proof of the two requested branches: faithful
parabolic-core actions supply the rank bound directly, replacing the
printed S₃×S₃ recognition and auxiliary dimension calculation. In the
contained case the elementary alternative, extraspecial structure,
center equality and Frattini inversion are proved independently above.
The standing noncentral seed action also proves L₁*≠1.

The final theorem is conditional only on ReducedOdd, the explicit standing
flag data and the permitted earlier geometry and 13.8.5(1) consequences.
Construction of ReducedOdd and the remaining three-primary branch belong
to the parent three-primary reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.951 (PDF p.968).
-/

@[expose] public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
variable {G : Type*} [Group G]
open CriticalGeometry Five

namespace Geometry
variable {L H V V₃ V₁ L₁ : Subgroup G} {T : Sylow 2 G} {c : CriticalPair L T H V}
    (s : Geometry c V₃ V₁ L₁)
include s

/-- Corrected 13.8.10 gives both rank-one quotients and V₁≤Uγ, with the
transvection alternative discharged by source 13.8.5 at the genuine endpoint. -/
theorem symmetry_and_line [Finite G]
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (c.Ugamma V₃)]
    (a : StarAction H (Source.UH H V₃) V₁)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hc : Nat.card (Source.starImage H c.Vgamma) ≤ 2) :
    Module.finrank (ZMod 2) (Additive
      (Source.UH H V₃ ⧸ (Source.DH (Source.UH H V₃) (c.Ugamma V₃)
        (c.Aone V₁)).subgroupOf (Source.UH H V₃))) = 1 ∧
    Module.finrank (ZMod 2) (Additive
      (c.Ugamma V₃ ⧸ (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).subgroupOf
        (c.Ugamma V₃))) = 1 ∧ V₁ ≤ c.Ugamma V₃ := by
  obtain ⟨hH, hγ, hline | haxis⟩ := corrected_rank_one_of_starImage H
    (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) V₁ s.Ugamma_le
    (s.actor_cards hc).1 s.Dgamma_kernel s.DH_strict s.comparison s.line_card
    (s.UH_le_endpoint.trans (c.normalizes_Ugamma V₃))
    (s.Ugamma_le.trans s.line_normalized)
  · exact ⟨hH, hγ, hline⟩
  · exact (no_endpoint_axis c a hs h135 s.UH_le_endpoint s.DH_strict haxis).elim

/-- Both normal-generation equalities, with their original seeds and actual edges. -/
theorem generations [Finite G] [IsElementaryAbelian 2 (Source.UH H V₃)]
    {p : ℕ} {M Vα : Subgroup G} (d : ReducedOdd p H L₁ T M Vα) :
    H = conjugateSpanBy (c.Ugamma V₃) H ⊔ (L₁ ⊔ T) ∧
      vertexGroup L T H c.gamma =
        conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔
          edgeGroup L T H c.gamma c.previous := by
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  obtain ⟨h, hplace⟩ := s.placement
  exact ⟨base_generation_of_core_placement d s.Ugamma_le s.base_core h
    ((map_mono s.Ugamma_le_Vgamma).trans hplace) s.Ugamma_star_ne,
    endpoint_generation c d s.base_edge s.endpoint_core s.base_core s.DH_kernel s.DH_strict⟩

/-- With the actual odd reduction, an endpoint star image of order at most
two contradicts 13.8.11. Both base and endpoint generation are proved here. -/
theorem false_of_actor_card_le_two [Finite G]
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    {p : ℕ} {M Vα : Subgroup G} (d : ReducedOdd p H L₁ T M Vα)
    (a : StarAction H (Source.UH H V₃) V₁)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hc : Nat.card (Source.starImage H c.Vgamma) ≤ 2) : False := by
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have hgen := (s.generations d).2
  have hnoncentral := c.noncentral_of_generation V₃ (Source.UH H V₃)
    s.V_le s.UH_le_endpoint hgen s.edge_commutator s.noncentral
  have hline := (s.symmetry_and_line a hs h135 hc).2.2
  have hlt := (starImage_lt_of_noncentral_and_line H (Source.UH H V₃)
    (c.Ugamma V₃) c.Vgamma V₁ s.UH_le s.Vgamma_le (s.line_le.trans s.UH_le)
    s.line_normalized s.Ugamma_le_Vgamma
    (s.Vgamma_le.trans (le_normalizer_conjugateSpanBy V₃ H))
    (s.UH_le_endpoint.trans (c.normalizes_Ugamma V₃)) s.core_commutator hnoncentral
    s.Ugamma_star_ne hline).1
  obtain ⟨hcU, hcV⟩ := s.actor_cards hc
  exact hlt.ne (eq_of_le_of_card_ge hlt.le (by rw [hcU, hcV]))

/-- The contained-L₁* three-primary exclusion. Its rank bound is established
by faithful center-fixing extraspecial automorphisms, without an assumed
rank-one contradiction or generation witness. -/
theorem contained_false [Finite G]
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    {M Vα : Subgroup G} (d : ReducedOdd 3 H L₁ T M Vα)
    (a : StarAction H (Source.UH H V₃) V₁)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hLM : L₁ ≤ M) (hTM : T ≤ M) (hTL : T ≤ normalizer (L₁ : Set G))
    (hne : Source.starImage H L₁ ≠ ⊥)
    (hLP : Source.starImage H L₁ ≤ Source.starImage H d.P) : False := by
  have hLH : L₁ ≤ H := le_sup_left.trans (d.generated ▸ le_sup_right)
  have hlt : Source.starImage H L₁ < Source.starImage H d.P :=
    lt_of_le_of_ne hLP (starImage_ne_of_outside d.P_le hLH hLM
      (s.base_core.trans (sup_le hLM hTM)) d.outside)
  let : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  obtain ⟨h, hplace⟩ := s.placement
  exact s.false_of_actor_card_le_two d a hs h135
    (contained_actor_card_le_two d hlt hne hTL s.Vgamma_le h hplace)

end Geometry

namespace Geometry
variable {L H V V₃ V₁ L₁ : Subgroup G} {T : Sylow 2 G} {c : CriticalPair L T H V}
    (s : Geometry c V₃ V₁ L₁)
include s

/-- The cyclic three-primary exclusion, using the actual parabolic placement
and a faithful action on P* of order three. -/
theorem cyclic_false [Finite G]
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    {M Vα : Subgroup G} (d : ReducedOdd 3 H L₁ T M Vα)
    (a : StarAction H (Source.UH H V₃) V₁)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hP : Nat.card (Source.starImage H d.P) = 3) : False := by
  obtain ⟨h, hplace⟩ := s.placement
  exact s.false_of_actor_card_le_two d a hs h135 (cyclic_actor_card_le_two d hP h hplace)

/-- Both rank-one branches of the three-primary reduction in 13.8.13.
Every actor bound, Frattini step, generation assertion and transvection
exclusion is discharged by the proofs above. -/
theorem rank_one_false [Finite G]
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    {M Vα : Subgroup G} (d : ReducedOdd 3 H L₁ T M Vα)
    (a : StarAction H (Source.UH H V₃) V₁)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hLM : L₁ ≤ M) (hTM : T ≤ M) (hTL : T ≤ normalizer (L₁ : Set G))
    (hne : Source.starImage H L₁ ≠ ⊥)
    (hcase : Nat.card (Source.starImage H d.P) = 3 ∨
      Source.starImage H L₁ ≤ Source.starImage H d.P) : False := by
  rcases hcase with hcyclic | hcontained
  · exact s.cyclic_false d a hs h135 hcyclic
  · exact s.contained_false d a hs h135 hLM hTM hTL hne hcontained

end Geometry

namespace Geometry
variable {L H V V₃ V₁ L₁ : Subgroup G} {T : Sylow 2 G} {c : CriticalPair L T H V}
    (s : Geometry c V₃ V₁ L₁)
include s

/-- The standing noncentral L₁-action on V₃/V₁ makes L₁* nontrivial.
This discharges the nontriviality premise of the contained-branch calculation. -/
theorem first_star_ne_of_seed [Finite G]
    (hseed : V₃ ≤ ⁅V₃, L₁⁆ ⊔ V₁) (hV₃ : Nat.card V₃ = 8) :
    Source.starImage H L₁ ≠ ⊥ := by
  intro hz
  have hLH : L₁ ≤ H := le_sup_left.trans (s.base_edge.symm ▸ inf_le_right)
  have hcore : L₁ ≤ Source.QH H := by
    have hh := le_sup_core_of_starImage_le hLH (show (⊥ : Subgroup G) ≤ H from bot_le)
      (show Source.starImage H L₁ ≤ Source.starImage H ⊥ by
        rw [hz]; exact bot_le)
    simpa only [bot_sup_eq] using hh
  have hc : ⁅V₃, L₁⁆ ≤ V₁ :=
    (commutator_mono (le_conjugateSpanBy V₃ H) hcore).trans s.core_commutator
  have hle := card_le_of_le (hseed.trans (sup_le hc le_rfl))
  rw [hV₃, s.line_card] at hle
  omega

/-- Both exclusions from the standing flag action and the permitted earlier
source consequences. No star nontriviality, rank-one contradiction or
normal-generation witness is an additional input. -/
theorem rank_one_false_of_seed [Finite G]
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    {M Vα : Subgroup G} (d : ReducedOdd 3 H L₁ T M Vα)
    (a : StarAction H (Source.UH H V₃) V₁)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hLM : L₁ ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hTL : (T : Subgroup G) ≤ normalizer (L₁ : Set G))
    (hseed : V₃ ≤ ⁅V₃, L₁⁆ ⊔ V₁) (hV₃ : Nat.card V₃ = 8)
    (hcase : Nat.card (Source.starImage H d.P) = 3 ∨
      Source.starImage H L₁ ≤ Source.starImage H d.P) : False :=
  s.rank_one_false d a hs h135 hLM hTM hTL (s.first_star_ne_of_seed hseed hV₃) hcase

/-- Final entry point with the actual quotient action constructed from the
standing core-centralization fact. The earlier 13.8.5 implication is universal
over presentations of that same conjugation action. -/
theorem rank_one_false_of_source [Finite G]
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    {M Vα : Subgroup G} (d : ReducedOdd 3 H L₁ T M Vα)
    (hs : Group.IsSolvable H)
    (h135 : ∀ a : StarAction H (Source.UH H V₃) V₁, TransvectionComponentConclusion a T)
    (hLM : L₁ ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hTL : (T : Subgroup G) ≤ normalizer (L₁ : Set G))
    (hseed : V₃ ≤ ⁅V₃, L₁⁆ ⊔ V₁) (hV₃ : Nat.card V₃ = 8)
    (hcase : Nat.card (Source.starImage H d.P) = 3 ∨
      Source.starImage H L₁ ≤ Source.starImage H d.P) : False := by
  obtain ⟨a⟩ := exists_starAction H (Source.UH H V₃) V₁
    (le_normalizer_conjugateSpanBy V₃ H) s.line_normalized s.core_commutator
  exact s.rank_one_false_of_seed d a hs (h135 a) hLM hTM hTL hseed hV₃ hcase

end Geometry

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
end
