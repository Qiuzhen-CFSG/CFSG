module

public import Stellmacher.SectionFiveToSeven.Result7_6
public import Stellmacher.SectionNine.GeneratedContext

/-!
# The corrected core noncontainment in (9.2)

For a generating neighbor of the normalized first edge, its intersection
with the next core is not contained in the initial core. Local transitivity
gives equal orders for the two core intersections, so a putative containment
would reverse the noncontainment already proved in (7.6)(c).

Source: Stellmacher, printed p.48 / PDF p.38. The abbreviated transcription
omits the negation. This result uses only Section Seven hypotheses and
supplies the corrected input to the normalized classification in (9.2).
-/

namespace Stellmacher.SectionNine

open Stellmacher.Later Stellmacher.SectionsFiveToSeven
open CosetGraphContext SevenSix

universe u

public theorem nine_two_core_noncontainment
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (m : Γ.Vertex) (hm : m ∈ neighborhood Γ cp.firstStep)
    (hgenerate : q Γ m ⊔ (stabilizer Γ cp.a ⊓ stabilizer Γ cp.firstStep) =
      stabilizer Γ cp.firstStep) :
    ¬ q Γ cp.firstStep ⊓ q Γ m ≤ q Γ cp.a := by
  have ha : cp.a ∈ neighborhood Γ cp.firstStep :=
    (mem_neighborhood_iff_adjacent Γ).2 (Γ.adjacent_symm cp.firstStep_adj)
  obtain ⟨actor, hactor⟩ := (lemma_seven_one h Γ).local_transitivity
    cp.firstStep ha hm
  have hfix : Γ.act (actor : G) cp.firstStep = cp.firstStep := by
    exact (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) (actor : G)).mp
      actor.property
  have hconj : q Γ cp.firstStep ⊓ q Γ m =
      (q Γ cp.firstStep ⊓ q Γ cp.a).map
        (MulAut.conj ((actor : G)⁻¹)).toMonoidHom := by
    calc
      q Γ cp.firstStep ⊓ q Γ m =
          q Γ (Γ.act (actor : G) cp.firstStep) ⊓
            q Γ (Γ.act (actor : G) cp.a) := by rw [hfix, hactor]
      _ = _ := by
        rw [q_act, q_act, Subgroup.map_inf _ _ _
          (MulAut.conj ((actor : G)⁻¹)).injective]
  have hcard : Nat.card ↥(q Γ cp.firstStep ⊓ q Γ m) =
      Nat.card ↥(q Γ cp.firstStep ⊓ q Γ cp.a) := by
    rw [hconj, Subgroup.card_map_of_injective
      (MulAut.conj ((actor : G)⁻¹)).injective]
  intro hle
  have heq : q Γ cp.firstStep ⊓ q Γ m = q Γ cp.firstStep ⊓ q Γ cp.a :=
    Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hle) hcard.ge
  apply (lemma_seven_six h Γ cp).neighbor_core_noncontainment m hm hgenerate
  rw [inf_comm, ← heq]
  exact inf_le_right


end Stellmacher.SectionNine
