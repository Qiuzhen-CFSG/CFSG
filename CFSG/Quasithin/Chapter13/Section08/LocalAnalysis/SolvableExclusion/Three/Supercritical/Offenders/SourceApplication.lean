module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Construction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.Selection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Selection

/-!
# The 13.8.13 prime restriction on U_H/V₁

This applies the offender selection to the literal source quotient. The
centralizer identity C_H(U_H/V₁)=O₂(H) proves faithfulness of its conjugation
representation. The output `QuadraticMember` of the earlier critical-pair
selection is converted to the shared D.2.1 definition, clearing the positive
rank in the ratio. The resulting prime conclusion has no additional local
offender-selection, movement or faithfulness premise.

The assembly owner qt-13-08-three-supercritical-reduction supplies the
standing elementary-abelian section and centralizer identity, the selected
pair and h from 13.8.8(2), and its complete earlier-source `QuadraticMember`
conclusion (produced by CriticalGeometry.Reorientation and FinalAssembly).
The action can be constructed by `exists_faithful_source_representation`;
any `Five.StarAction` on this literal quotient gives the same action, by
`Five.StarAction.action_eq`. The universal D.2.13(1) implication remains an
authorized earlier-source input owned by qt-d-02.

Solvability and minimality in the genuine Hz family have already been used
to construct `OddConstruction`. Its generation clause suffices here;
Frattini irreducibility and D.2.17 are not needed for the prime restriction.
This conditional result does not assert the full solvable-overgroup theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the standing
setup on p.946, 13.8.8(2) on p.949, and 13.8.13 on pp.950–951.
-/

@[expose] public section

universe u v
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterD
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
variable {G : Type u} [Group G] [Finite G]
variable {E : Type v} [AddCommGroup E] [Module (ZMod 2) E]
variable {H : Subgroup G}

/-- The actual earlier critical-geometry bound is exactly D.2.1 Q-membership. -/
theorem Q_of_quadraticMember
    (ρ : Representation (ZMod 2) (Source.Hstar H) E)
    {A : Subgroup (Source.Hstar H)}
    (hA : CriticalGeometry.Reorientation.QuadraticMember ρ A) : A ∈ Q ρ := by
  refine ⟨hA.1, hA.2.1, ?_⟩
  exact (actionRatio_le_nat_iff ρ hA.1 2).mpr hA.2.2

/-- Apply the earlier 13.8.8(2) conclusion to the actual quotient U_H/V₁.
Faithfulness follows from the source centralizer identity, and the minimal
cubic offender and its nontrivial prime-core action are constructed. -/
theorem prime_restriction_on_Utilde
    (hD213 : D213PrimeRestriction.{u, u})
    {p : ℕ} {L L₁ T M V Vα V₃ V₁ : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (c : OddConstruction p H L₁ T M Vα)
    (e : CriticalGeometry.CriticalPair L T H V)
    (hV₃ : V₃ ≤ V) (h : H)
    (hα : e.Vgamma.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Vα ≤ (L₁ ⊔ T).pCoreIn 2)
    (a : Five.StarAction H (Source.UH H V₃) V₁)
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁)
    (hQ : CriticalGeometry.Reorientation.QuadraticMember (linearAction a)
      (Source.starImage H (e.Ugamma V₃))) : p = 3 ∨ p = 5 := by
  exact prime_restriction_of_Q hD213 c e (conjugateSpanBy_mono hV₃ le_rfl)
    h hα hplace (linearAction a)
    (linearAction_injective a (a.injective_of_kernel hk))
    (Q_of_quadraticMember (linearAction a) hQ)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
end
