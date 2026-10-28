module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Selection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.PrimeReduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Assembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.RankOne.Contradiction

/-!
# Assembling the odd reduction and the rank-one exclusions

The supercritical construction supplies the actual subgroup P and restricts
its prime to three or five. At three the proved rank-one argument excludes
both a cyclic star image and containment of L₁* in P*. Thus the only cases
left before `ReducedFive` are the noncontained elementary-nine and
exponent-three extraspecial-27 cases, on that same constructed subgroup.

This is a reduction to those two cases, not their exclusion. In particular,
the conditional dimension and rank endpoints in `Three.Noncontained` do not
yet construct the action or elementary subgroup required to close them.
All inputs here precede 13.8.13: the standing flag, the complete selected
13.8.8 geometry, 13.8.5, the 13.8.12 residual alternative and universal
D.2.13(1). No small odd subgroup or rank-one contradiction is assumed by
`exists_five_or_noncontained`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed pp.950–951 (PDF pp.967–968).
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three
open CriticalGeometry Five
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The two rank-one cases are impossible, leaving exactly the noncontained
elementary-nine or extraspecial-27 alternatives on the original P*. -/
theorem noncontained_of_three
    {H L L₁ M V V₃ V₁ Vα : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    {c : CriticalPair L T H V} (s : RankOne.Geometry c V₃ V₁ L₁)
    (d : ReducedOdd 3 H L₁ T M Vα)
    (a : StarAction H (Source.UH H V₃) V₁)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hLM : L₁ ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hTL : (T : Subgroup G) ≤ normalizer (L₁ : Set G))
    (hseed : V₃ ≤ ⁅V₃, L₁⁆ ⊔ V₁) (hV₃ : Nat.card V₃ = 8) :
    ¬ Source.starImage H L₁ ≤ Source.starImage H d.P ∧
      ((IsElementaryAbelian 3 (Source.starImage H d.P) ∧
        Nat.card (Source.starImage H d.P) = 3 ^ 2) ∨
       (IsExtraspecial 3 (Source.starImage H d.P) ∧
        Nat.card (Source.starImage H d.P) = 3 ^ 3 ∧
        ∀ x : Source.starImage H d.P, x ^ 3 = 1)) := by
  have hnot := s.rank_one_false_of_seed d a hs h135 hLM hTM hTL hseed hV₃
  refine ⟨fun h => hnot (Or.inr h), ?_⟩
  exact d.Pstar_small.resolve_left (fun h => hnot (Or.inl h))

/-- Construct the supercritical subgroup and discharge both rank-one
branches. The remaining disjunct explicitly names the two unclosed cases;
it is not an assumption of the five-primary conclusion. -/
theorem exists_five_or_noncontained
    (hD213 : Supercritical.Offenders.D213PrimeRestriction.{u, u})
    {H L L₁ L₁plus G₁ M V V₃ V₁ Vα : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    {c : CriticalPair L T H V} (s : RankOne.Geometry c V₃ V₁ L₁)
    (hs : Group.IsSolvable H) (hr : IsStronglyQuasithin H)
    (hH : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hline : V₁ ≤ V₃) (hVT : V ≤ T)
    (hG₁ : G₁ ≤ normalizer (V₁ : Set G))
    (hres : ResidualAlternative L L₁ L₁plus (residualInM H M))
    (hplus : L₁plus ≤ L₁)
    (a : StarAction H (Source.UH H V₃) V₁)
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁)
    (hQ : Reorientation.QuadraticMember (Supercritical.Offenders.linearAction a)
      (Source.starImage H (c.Ugamma V₃)))
    (h : H) (hα : c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Vα ≤ (L₁ ⊔ T).pCoreIn 2)
    (h135 : TransvectionComponentConclusion a T)
    (hLM : L₁ ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hTL : (T : Subgroup G) ≤ normalizer (L₁ : Set G))
    (hseed : V₃ ≤ ⁅V₃, L₁⁆ ⊔ V₁) (hV₃ : Nat.card V₃ = 8) :
    Nonempty (ReducedFive H L₁ T M Vα) ∨
      ∃ d : ReducedOdd 3 H L₁ T M Vα,
        ¬ Source.starImage H L₁ ≤ Source.starImage H d.P ∧
        ((IsElementaryAbelian 3 (Source.starImage H d.P) ∧
          Nat.card (Source.starImage H d.P) = 3 ^ 2) ∨
         (IsExtraspecial 3 (Source.starImage H d.P) ∧
          Nat.card (Source.starImage H d.P) = 3 ^ 3 ∧
          ∀ x : Source.starImage H d.P, x ^ 3 = 1)) := by
  have hne : V₁ ≠ ⊥ := by
    intro he
    have hc := s.line_card
    rw [he, Nat.card_unique] at hc
    contradiction
  have hp : IsPGroup 2 V₁ :=
    (IsElementaryAbelian.isPGroup 2 (Source.UH H V₃)).of_injective
      (inclusion s.line_le) (inclusion_injective s.line_le)
  obtain ⟨p, hp35, ⟨d⟩⟩ := Supercritical.exists_reducedOdd hD213 hs hr hne hp
    (hline.trans (s.seed_le.trans (hVT.trans le_sup_right))) hG₁ hH hres hplus
    c s.seed_le h hα hplace a hk hQ
  rcases hp35 with rfl | rfl
  · exact Or.inr ⟨d, noncontained_of_three s d a hs h135 hLM hTM hTL hseed hV₃⟩
  · exact Or.inl ⟨{
      P := d.P
      P_le := d.P_le
      P_isPGroup := d.P_isPGroup
      Pstar_normal := d.Pstar_normal
      moved := d.moved
      outside := d.outside
      generated := d.generated
      irreducible := d.irreducible }⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three

end
