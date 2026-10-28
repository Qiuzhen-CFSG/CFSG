module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.Source
public import CFSG.Quasithin.Chapter6.SourceDefs.ReducedImage

/-!
# The original ordinary A₆ setup from its chosen module

The natural module has sixteen elements. Its T-invariance therefore gives
an actual nested normal flag of orders two, four, and eight inside the
original Sylow group. The A₆ quotient is centerless, so the action through
L/O₂(L) is the identical action through L/O₂,Z(L). The source's reduced
module inclusion and T-normalization of L come from the literal Irr⁺ choice.

Thus the earlier natural-module conclusion constructs the entire unchanged
NaturalSetup. No independent flag, quotient comparison, or coordinate action
is assumed. T-invariance and the natural-module classification remain genuine
preceding source inputs.
Source: Aschbacher--Smith 13.3.2(3), Notation 13.2.1, and Hypothesis 13.7.1,
printed pp.885,877,935, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem centralCore_eq_twoCore_of_six
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) : centralCore L = pCore 2 L := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6)), card_bot]
  change (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) = pCore 2 L
  rw [hz]
  exact QuotientGroup.ker_mk' _

theorem exists_original_six_setup_of_chosen_module
    (h : Counterexample T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hmodel : Chapter6.Source.IsConjugationModel L V
      (alternatingNaturalRepresentation (Fin 6))) :
    ∃ V₁ V₂ V₃ : Subgroup G, Nonempty
      (NaturalSetup T L V V₁ V₂ V₃ (normalizer (L : Set G)) (normalizer (V₁ : Set G))) := by
  obtain ⟨e, f, hf⟩ := hmodel
  have hc : Nat.card V = 16 := by
    have hn := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := natural (Fin 6))
    rw [Nat.card_zmod, finrank_natural_even (Fin 6) (by decide)] at hn
    exact (Nat.card_congr (f.toEquiv.trans Multiplicative.toAdd)).trans (by simpa using hn)
  obtain ⟨V₁,V₂,V₃,h12,h23,h3V,h1,h2,h3,hT1,hT2,hT3⟩ :=
    Chapter13.Section03.A5Setup.exists_invariant_flag D.le_sylow hTV hc
  have hn : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) := sup_le D.normalizes hTV
  let ec := QuotientGroup.quotientMulEquivOfEq (centralCore_eq_twoCore_of_six e)
  refine ⟨V₁,V₂,V₃,⟨{
    counterexample := h
    normalizes_L := D.sylow_normalizes_component
    normalizes_V := hn
    local_quotient := ec.trans e
    module_in_reduced := ?_
    coordinate := f
    conjugation := ?_
    line_le_plane := h12
    plane_le_seed := h23
    seed_le := h3V
    line_card := h1
    plane_card := h2
    seed_card := h3
    line_stable := hT1
    plane_stable := hT2
    seed_stable := hT3
    first_normalizer := rfl
    local_normalizer := rfl
    chosen := D }⟩⟩
  · rw [Chapter6.Source.reducedSubgroup_eq_map]
    exact D.le_reduced
  · intro l v
    change f (V.normalizerMonoidHom ⟨l.val, hn (mem_sup_left l.property)⟩ v) =
      Multiplicative.ofAdd ((alternatingNaturalRepresentation (Fin 6))
        (e (QuotientGroup.mk' (pCore 2 L) l)) (f v).toAdd)
    apply f.symm.injective
    rw [f.symm_apply_apply]
    exact Subtype.ext (hf l v).symm

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
