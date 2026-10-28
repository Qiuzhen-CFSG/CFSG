module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.RankTwo
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Alternatives

/-!
# Excluding the order-four actor from the common-center equality case

Faithfulness on the literal image of D_H forces every nontrivial subgroup
of Uγ* to move that image. In particular each of the two involution factors
has nonzero displacement on it. Both displacement planes therefore contain
the common line of order two. Their join has order at most eight, contrary
to the order-sixteen full displacement supplied by the factor analysis.

This proves the conditional assembly of the two independent construction
steps. `rankOneFactors_of_alternatives` still requires both actor alternatives
and the F.9.16 equality-case geometry; it is not a source-level existence
proof for the factors.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, using F.9.16(2), printed pp.323–324.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five

private theorem moved_mono_actor {W : Type*} [Group W]
    {A B : Subgroup (MulAut W)} (hAB : A ≤ B) (D : Subgroup W) :
    commutatorSubgroup A W D ≤ commutatorSubgroup B W D := by
  apply Subgroup.closure_mono
  rintro _ ⟨a, d, hd, rfl⟩
  exact ⟨⟨a, hAB a.property⟩, d, hd, rfl⟩

theorem moved_ne_bot_of_faithful_on {W K : Type*} [Group W] [Group K]
    (ρ : K →* MulAut W) (A B : Subgroup K) (D : Subgroup W)
    (hAB : A ≤ B) (hA : A ≠ ⊥)
    (hf : ∀ b ∈ B, (∀ d ∈ D, ρ b d = d) → b = 1) :
    commutatorSubgroup (A.map ρ) W D ≠ ⊥ := by
  intro he
  apply hA
  apply bot_unique
  intro b hb
  apply hf b (hAB hb)
  intro d hd
  have hm : d⁻¹ * ρ b d ∈ commutatorSubgroup (A.map ρ) W D :=
    subset_closure ⟨⟨ρ b, mem_map_of_mem ρ hb⟩, d, hd, rfl⟩
  rw [he, mem_bot] at hm
  exact (inv_mul_eq_one.mp hm).symm

theorem no_rank_two_of_faithful_common_center {W K : Type*} [CommGroup W] [Finite W]
    [Group K] (ρ : K →* MulAut W) (A B C : Subgroup K) (D Z : Subgroup W)
    (hgen : C = A ⊔ B) (hneA : A ≠ ⊥) (hneB : B ≠ ⊥)
    (hf : ∀ c ∈ C, (∀ d ∈ D, ρ c d = d) → c = 1)
    (hZ : Nat.card Z = 2)
    (hA : Nat.card (commutatorAction (A.map ρ) W) = 4)
    (hB : Nat.card (commutatorAction (B.map ρ) W) = 4)
    (hline : commutatorSubgroup (C.map ρ) W D ≤ Z)
    (hfull : Nat.card (commutatorAction (C.map ρ) W) = 16) : False := by
  have hAC : A ≤ C := hgen ▸ le_sup_left
  have hBC : B ≤ C := hgen ▸ le_sup_right
  apply no_rank_two_common_center (A.map ρ) (B.map ρ) D Z hZ hA hB
    (moved_ne_bot_of_faithful_on ρ A C D hAC hneA hf)
    (moved_ne_bot_of_faithful_on ρ B C D hBC hneB hf)
    ((moved_mono_actor (map_mono hAC) D).trans hline)
    ((moved_mono_actor (map_mono hBC) D).trans hline)
  rw [hgen, Subgroup.map_sup] at hfull
  exact hfull

variable {G : Type*} [Group G] [Finite G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

theorem RankTwoFactors.impossible [IsMulCommutative UH]
    {a : StarAction H UH V₁} {P Uγ A₁ : Subgroup G}
    (f : RankTwoFactors a P Uγ) (c : CommonCenterOnDH a Uγ A₁) : False := by
  have hA : f.first ≠ ⊥ := by
    intro he
    have hc := f.first_card
    rw [he] at hc
    simp at hc
  have hB : f.second ≠ ⊥ := by
    intro he
    have hc := f.second_card
    rw [he] at hc
    simp at hc
  exact no_rank_two_of_faithful_common_center a.action f.first f.second
    (Source.starImage H Uγ) (tildeImage UH V₁ (Source.DH UH Uγ A₁))
    (tildeImage UH V₁ A₁) f.generated hA hB c.faithful c.center_card
    f.first_plane f.second_plane c.displacement_le f.moved_card

theorem rankOneFactors_of_alternatives [IsMulCommutative UH]
    (a : StarAction H UH V₁) (P Uγ A₁ : Subgroup G)
    (halternatives : Nonempty (RankOneFactors a P Uγ) ∨ Nonempty (RankTwoFactors a P Uγ))
    (hgeometry : Nat.card (Source.starImage H Uγ) = 4 →
      (FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)).index = 16 →
      CommonCenterOnDH a Uγ A₁) : Nonempty (RankOneFactors a P Uγ) := by
  rcases halternatives with h | h
  · exact h
  · obtain ⟨f⟩ := h
    exact (f.impossible (hgeometry f.actor_card f.fixed_index)).elim

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
