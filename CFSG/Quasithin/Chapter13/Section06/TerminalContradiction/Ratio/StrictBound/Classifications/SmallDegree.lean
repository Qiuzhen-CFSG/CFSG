module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.Alternatives
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.Quotient

/-!
# Intrinsic classification of small-degree component actions

A quasisimple group is its own generalized Fitting subgroup. Thus a
faithful irreducible binary action of the marked component itself satisfies
the genuine B.4 hypotheses when the inherited SQTK hypothesis is supplied.
For degree at most four, an explicit involution supplies an actual rank-one
quadratic actor, so the full B.4 classifications give the competing models.
The involution is a structural input; it is not assumed to have any special
action on the module. Excluding those models remains with the terminal
classification assembly.

Source: Aschbacher–Smith, B.4.2/B.4.5 and the constituent reduction for
terminal §13.6, printed pp.86–87 and 935 (1 March 2004 manuscript).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications
universe u v

private theorem fitting_eq_top {L : Type*} [Group L] (hL : IsQuasisimple L) :
    generalizedFitting L = ⊤ := by
  let := hL
  apply top_unique
  exact component_le_generalizedFitting L ⊤
    ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩

variable {L : Type u} [Group L] [Finite L] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (σ : Representation (ZMod 2) L V)

/-- Intrinsic use of B.4 requires no separate component construction:
quasisimplicity makes F*(L) equal to L. -/
theorem b4Hypotheses_intrinsic {𝒦 : GroupClass.{u}}
    (hsq : IsSQTK 𝒦 L) (hf : Function.Injective σ)
    (hL : IsQuasisimple L) (hi : σ.IsIrreducible) : B4Hypotheses 𝒦 σ := by
  let := hL
  let e : generalizedFitting L ≃* L :=
    (MulEquiv.subgroupCongr (fitting_eq_top hL)).trans topEquiv
  refine ⟨hsq, hf, IsQuasisimple.of_mulEquiv e.symm, ?_⟩
  apply (irreducible_comp_surjective_iff _ ?_ σ).mpr hi
  intro g
  exact ⟨e.symm g, e.apply_symm_apply g⟩

/-- A faithful irreducible action of degree at most four on a centerless
quasisimple SQTK group with an involution must have one of the competing
group models. Both source classifications remain complete universal inputs. -/
theorem competitors_of_small_degree {𝒦 : GroupClass.{u}}
    (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hsq : IsSQTK 𝒦 L) (hf : Function.Injective σ)
    (hL : IsQuasisimple L) (hi : σ.IsIrreducible) (hz : center L = ⊥)
    (t : L) (ht : orderOf t = 2) (hdim : Module.finrank (ZMod 2) V ≤ 4) :
    ClassicalCompetitor L ∨ FixedCompetitor L := by
  let e : generalizedFitting L ≃* L :=
    (MulEquiv.subgroupCongr (fitting_eq_top hL)).trans topEquiv
  have hz' : center (generalizedFitting L) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (centerCongr e).toEquiv, hz]
    exact Subgroup.card_bot
  have hq := quadraticRatio_le_two_of_finrank_le_four σ t ht hdim
  rcases competitors_of_small_ratio σ hB42 hB45
      (b4Hypotheses_intrinsic σ hsq hf hL hi) hz' hq with hc | hf
  · exact .inl (hc.transport e)
  · exact .inr (hf.transport e)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications
