module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateDefs
public import CFSG.Quasithin.Chapter6.Section01.SourceModelKernel
public import Theory.GroupTheory.NormalizerActionSolvability
public import Theory.GroupTheory.PResidual.Defs
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic

/-!
# The nonsolvable action in the field branch of 6.1.14

The last paragraph of 6.1.14(5) compares two actual normalizer actions.  The
action of a local residual on the conjugate line is nonsolvable because its
faithful natural quotient is SL₂ over a field of degree greater than one.
This file supplies the formal transport needed for that comparison.  The
Sylow, local-component and normalizer-control facts used to construct the
local residual remain explicit hypotheses of the source assembly.

Source: Aschbacher--Smith, printed pp.671--672 (PDF pp.688--689).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G]

/-- Faithfulness makes the natural SL₂ quotient a quotient of the actual
conjugation image. For degree greater than one it is perfect and nontrivial. -/
theorem normalizerAction_not_solvable_of_natural
    {K Z : Subgroup G} {m : ℕ} (h : IsNaturalModule K Z m) (hm : 1 < m) :
    ¬ Group.IsSolvable (normalizerAction K Z).range := by
  obtain ⟨F, _, _, _, hF, hmodel⟩ := h
  have hsize : 2 < Nat.card F := by
    rw [hF]
    calc
      2 = 2 ^ 1 := by decide
      _ < 2 ^ m := pow_lt_pow_right₀ (by decide) hm
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hsize
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hsize
  have hc := hmodel.centralizer_eq_core (Representation.specialLinearNatural_injective 2)
  have hn := hmodel.normalizes
  obtain ⟨e, _, _⟩ := hmodel
  apply normalizerAction_not_solvable_of_quotient K Z hn
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  · rw [hc]
    apply map_mono
    intro k hk
    change e (QuotientGroup.mk' (pCore 2 K) k) = 1
    have he : QuotientGroup.mk' (pCore 2 K) k = 1 :=
      (QuotientGroup.eq_one_iff k).mpr hk
    rw [he, map_one]
  · exact Group.IsPerfect.not_isSolvable _

/-- The literal embedded two-residual O²(N_L(U)). This is not O₂(N_L(U)). -/
@[expose] def fieldLocalResidual (L U : Subgroup G) : Subgroup G :=
  let N := L ⊓ normalizer (U : Set G)
  (pResidual 2 N).map N.subtype

/-- The pending local-component and module calculation in 6.1.14(5).
The actor is O²(N_L(U)); the module is an actual conjugate of Z; its field
has half the original degree. The conjugator may change when arranging the
source Sylow subgroups. No escape conclusion is part of this input. -/
@[expose] def FieldNaturalLocalAction (L M B Z : Subgroup G) (n : ℕ) : Prop :=
  2 < n → ∀ (g : G) (U : Subgroup G), U ≠ ⊥ →
    ChapterE.subgroupCorank B U = n →
    IsInvolutoryFieldFixedSpace L M B U n →
    B.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) →
    B ≤ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G) →
    ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G) →
    centralizer (Z : Set G) ≤ M →
    ∃ (m : ℕ) (x : G), n = 2 * m ∧
      IsNaturalModule (fieldLocalResidual L U) (Z.map (MulAut.conj x).toMonoidHom) m

/-- The terminal contradiction of 6.1.14(5), conditional on the earlier
normalizer-control, solvable-action and local natural-module inputs. -/
theorem fieldConjugateEscape_of_naturalLocalAction
    (L M B Z : Subgroup G) (n : ℕ)
    (hcontrol : centralizer (Z : Set G) ≤ M → normalizer (Z : Set G) ≤ M)
    (hsolv : Group.IsSolvable (normalizerAction M Z).range)
    (hloc : FieldNaturalLocalAction L M B Z n) :
    FieldConjugateEscape L M B Z n := by
  intro hn g U hU hcor hfield hcentral hnormal hnoncentral hI
  obtain ⟨m, x, hnm, hnatural⟩ :=
    hloc hn g U hU hcor hfield hcentral hnormal hnoncentral hI
  have hns := normalizerAction_not_solvable_of_natural hnatural (by omega)
  have hK : fieldLocalResidual L U ≤
      normalizer (Z.map (MulAut.conj x).toMonoidHom : Set G) := by
    obtain ⟨_, _, _, _, _, hmodel⟩ := hnatural
    exact hmodel.normalizes
  exact centralizer_not_le_of_nonsolvable_conjugate_action M Z
    (fieldLocalResidual L U) x hcontrol hsolv hK hns hI

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
