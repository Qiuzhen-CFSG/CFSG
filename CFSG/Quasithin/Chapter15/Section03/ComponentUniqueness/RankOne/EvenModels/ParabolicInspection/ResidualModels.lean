module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.Data
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.LinearTwo
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.UnitaryThree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.Symplectic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.G2
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.Triality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.Ree

/-!
# Residual inspection of larger-field invariant parabolics

The cubic two-core index, solvability of O^{3′}, and the source four-group
constrain the actual invariant parabolic. The model calculations leave
PSL₂ and PSL₃ in even field degree, or PSU₃, and identify the intersection
with the Borel in the component action quotient.

The assembly exhausts the incoming catalogue, including genuine triality,
the permitted Ree fields, and the small derived groups. Simplicity and
component perfectness identify the simple PSL₃ model with its central
quotient. The separate PSL₃(4) central two-covers remain allowed, whereas
the G₂(4) covers are excluded through their actual central quotient.
Parabolic recognition remains the explicit premise `QuotientParabolic`;
the parent supplies it and lifts the Borel equality upstairs.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, printed p.1140; 1.1.5(3)(a)--(c), pp.501--502; A.2.3--4, p.33.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The larger-field residual inspection, conditional only on recognition
of the actual quotient intersection as a maximal invariant parabolic.
The linear-three output retains the permitted nontrivial central covers. -/
theorem residual_inspection_of_model (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} {n : ℕ} (hn : 1 < n)
    (hm : Model L z n) (hp : QuotientParabolic c) :
    BorelModel L n ∧
      c.toComponentAction.image M ⊓ c.toComponentAction.image L =
        ChapterF.Source.borel (c.toComponentAction.image L) (c.toComponentAction.image S) := by
  cases hm with
  | simple hs hm _ =>
    cases hm with
    | linearTwo _ iso => exact linearTwo_inspection c iso hp
    | unitaryThree _ iso =>
      exact ⟨.unitaryThree iso, unitaryThree_residual_inspection c hn hs iso hp⟩
    | rankTwo hm =>
      cases hm with
      | linear _ iso =>
        let : IsSimpleGroup L := hs
        let : Theory.GroupTheory.IsQuasisimple (L.subgroupOf I) := c.component.2
        let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
          (f := (subgroupOfEquivOfLe c.component_le).toMonoidHom)
          (subgroupOfEquivOfLe c.component_le).surjective
        have hc : center L = ⊥ := by
          rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with h | h
          · exact h
          · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp h)).elim
        let e : (L ⧸ center L) ≃* L :=
          (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
        have hq := iso.of_mulEquiv e
        obtain ⟨he, hB⟩ := linearThree_residual_inspection c hn hp hq
        exact ⟨.linearThree he hq, hB⟩
      | symplectic _ iso => exact (symplectic_residual_exclusion c hn iso hp).elim
      | g2 _ iso => exact (g2_residual_exclusion c hn hs iso hp).elim
      | triality _ iso => exact (triality_residual_exclusion c hn hs iso hp).elim
      | ree_f4 m hm _ iso => exact (ree_residual_exclusion c hm hs iso hp).elim
      | symplectic_derived hf _ => omega
      | g2_derived hf _ => omega
      | tits hf _ => omega
    | binaryLinear hf _ _ _ => omega
  | linearThreeCover hf _ iso _ =>
    have hq : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n) := by
      simpa [hf] using iso
    obtain ⟨he, hB⟩ := linearThree_residual_inspection c hn hp hq
    exact ⟨.linearThree he hq, hB⟩
  | g2Cover _ hc iso _ => exact (g2_cover_residual_exclusion c hc iso hp).elim
  | alternatingSix hf _ _ => omega

/-- The original conditional interface, retained with its exact assumptions. -/
theorem residual_inspection (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (_hz : SourceInvolution S M z) {n : ℕ} (hn : 1 < n)
    (hm : Model L z n) (hp : QuotientParabolic c) :
    BorelModel L n ∧
      c.toComponentAction.image M ⊓ c.toComponentAction.image L =
        ChapterF.Source.borel (c.toComponentAction.image L) (c.toComponentAction.image S) :=
  residual_inspection_of_model c hn hm hp

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
