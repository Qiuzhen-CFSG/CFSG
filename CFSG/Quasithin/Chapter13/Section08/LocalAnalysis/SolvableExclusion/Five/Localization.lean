module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.Data
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.NoTransvections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SecondActor

/-!
# Localization of the five-primary rank-one action

Once the geometric and second-actor constructions have been supplied,
`support_consequences` proves the remaining support conditions needed by
`StarAction.second_summand_fixed`: fixation modulo V₁ of the canonical
second lift, invariance under Vγ, disjointness from the first support, and
the moved-space bound. It also supplies the competing moved-point witness
for B₂ on that same second support. No final contradiction is taken as input.

`exists_localization` constructs both inputs from the supplied faithful
rank-one factor action, the minimal solvable five-primary reduction, and
the genuine standing and earlier source facts. The endpoint construction
derives symmetry, generation and the rank bound; the actor construction
then proves that there are two factors and constructs B₂ inside the original
Vγ. All support conclusions concern those same factors and canonical lifts.

The imported endpoint results also export the actual reversed critical pair,
its quotient equivalence, and exclusion of nonidentity transvections on both
endpoint quotients. The remaining input `hplacement` is the conjugate-core
placement in 13.8.8(2), using left conjugation by the inverse of the source's
right-conjugating element. The parent five-primary exclusion constructs the
rank-one factor input and retains the final application of
`StarAction.second_summand_fixed` and its contradiction with the moved point.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951 (PDF p.968), final two paragraphs.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization
open Subgroup
open CriticalGeometry
variable {G : Type*} [Group G] [Finite G]
variable {L T H V V₃ V₁ P : Subgroup G}
variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]
variable [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Derived action and commutator facts for the actual two factor supports.
The two construction inputs remain explicit until source assembly. -/
theorem support_consequences
    (c : CriticalPair L T H V)
    (a : StarAction H (Source.UH H V₃) V₁) (hf : Function.Injective a.action)
    (f : RankOneFactors a P (c.Ugamma V₃))
    (geo : GeometricBounds c V₃ V₁)
    (second : SecondFactor a f c.Vgamma (c.Aone V₁)) :
    ⁅liftTilde (Source.UH H V₃) V₁ (f.factors.support second.second), c.Ugamma V₃⁆ ≤ V₁ ∧
    (∀ b : a.actors c.Vgamma, ∀ w ∈ f.factors.support second.second,
      b • w ∈ f.factors.support second.second) ∧
    (∃ b : a.actors second.B₂, ∃ w ∈ f.factors.support second.second, b • w ≠ w) ∧
    Disjoint (f.factors.support ⟨0, f.factors.count_pos⟩)
      (f.factors.support second.second) ∧
    2 < Nat.card (tildeImage (Source.UH H V₃) V₁ ⁅Source.UH H V₃, c.Ugamma V₃⁆) := by
  refine ⟨f.remaining_lift_fixed a hf geo.Ugamma_le _ second.second_ne_zero,
    f.factors.support_invariant a _ _ second.normalizes_second,
    f.factors.exists_moved_on_support a hf _ _ ?_ second.moves_second, ?_, ?_⟩
  · have hle : Source.starImage H second.B₂ ≤ Source.starImage H c.Vgamma :=
      map_mono (fun _ hx => second.B₂_le hx)
    exact hle.trans second.normalizes_second
  · apply f.factors.support_disjoint
    intro he
    exact second.second_ne_zero (congrArg Fin.val he.symm)
  · rw [← a.commutatorAction_eq_tildeImage _ geo.Ugamma_le, f.moved_card]
    decide

open CriticalGeometry.Reorientation
open scoped IsMulCommutative

/-- The complete localization output for the last two paragraphs of 13.8.13.
The standing flag and universal earlier geometry are `s`; `h135` is the
complete earlier 13.8.5 implication, and `hplacement` is 13.8.8(2).
Neither geometry, symmetry, generation, factor count, second actor, support
invariance nor a moved point is assumed. The five-factor construction remains
the separate input `f`, as required by this intermediate source deduction. -/
theorem exists_localization {L₁ G₁ M Vα : Subgroup G} {T : Sylow 2 G}
    (c : CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (a : StarAction H (Source.UH H V₃) V₁) (hf : Function.Injective a.action)
    (reduced : ReducedFive H L₁ T M Vα)
    (f : RankOneFactors a reduced.P (c.Ugamma V₃))
    (hminimal : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hs : Group.IsSolvable H)
    (s : EndpointGeometry.SourceInputs c V₃ V₁ L₁ G₁ M)
    (h135 : (∃ h : H, (EndpointGeometry.centerAction a).action h ≠ 1 ∧
      binaryLinear ((EndpointGeometry.centerAction a).action h) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) →
      FullModelConclusions L L₁ T (le_sup_left.trans hminimal.prop.1.2)
        (EndpointGeometry.centerAction a))
    (hplacement : ∃ h : H,
      c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    GeometricBounds c V₃ V₁ ∧
      ∃ second : SecondFactor a f c.Vgamma (c.Aone V₁),
        ⁅liftTilde (Source.UH H V₃) V₁ (f.factors.support second.second), c.Ugamma V₃⁆ ≤ V₁ ∧
        (∀ b : a.actors c.Vgamma, ∀ w ∈ f.factors.support second.second,
          b • w ∈ f.factors.support second.second) ∧
        (∃ b : a.actors second.B₂, ∃ w ∈ f.factors.support second.second, b • w ≠ w) ∧
        Disjoint (f.factors.support ⟨0, f.factors.count_pos⟩)
          (f.factors.support second.second) ∧
        2 < Nat.card (tildeImage (Source.UH H V₃) V₁
          ⁅Source.UH H V₃, c.Ugamma V₃⁆) := by
  let _ : IsElementaryAbelian 2 V :=
    IsElementaryAbelian.of_le (show V ≤ Source.VH H V from le_conjugateSpanBy V H)
  have geo := EndpointGeometry.geometric_bounds c a hf reduced f hminimal hs s h135
  obtain ⟨second⟩ := SecondActor.exists_secondFactor c a hf reduced f hminimal hs geo
    s.seed_le hplacement
  exact ⟨geo, second, support_consequences c a hf f geo second⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization
end
