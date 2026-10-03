module

public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs

/-!
# Local actor and commutator inputs for Stellmacher (9.5)

The prescribed actor is an involution in the terminal stabilizer and
normalizes its neighbor-center module. The commutator is contained in
both prescribed modules, centralizes the entire first-step module, and
is not contained in the terminal center. These conclusions use only
the genuine local Section Nine context; no ambient hypothesis is moved
from H to the generated group.

This is the setup for the transvection argument on printed pp.52–53
of `refs/files/stellmacher-n-group.pdf`, not the dichotomy itself.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem nine_five_transvection_inputs
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (prev : ctx.Γ.Vertex) (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ prev) :
    CosetGraphContext.IsInvolution actor ∧
      IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') ∧
      Subgroup.zpowers actor ≤ GAt ctx.Γ ctx.criticalPath.a' ∧
      Subgroup.zpowers actor ≤ Subgroup.normalizer
        (VAt ctx.Γ ctx.criticalPath.a' : Set G) ∧
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
        VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ prev ∧
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
        Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G) ∧
      ¬ ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.a' := by
  have hlong := (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
    ctx.commutator_eq).longer_case hb
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) := hlong.1
  have hinvolution : CosetGraphContext.IsInvolution actor := by
    refine ⟨?_, elemPow_eq_one_of_isElementaryAbelian actor hactor.1⟩
    intro hone
    exact hactor.2 (hone ▸ (QAt ctx.Γ ctx.criticalPath.a').one_mem)
  have hcyclic : Subgroup.zpowers actor ≤ VAt ctx.Γ ctx.criticalPath.firstStep :=
    (Subgroup.zpowers_le).mpr hactor.1
  have hlocal : Subgroup.zpowers actor ≤ GAt ctx.Γ ctx.criticalPath.a' :=
    hcyclic.trans (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2
  have hnormalizer := hlocal.trans
    (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a')
  have hcommutator := Subgroup.le_normalizer_iff_commutator_le_left.mp hnormalizer
  have hcentral : ⁅⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆,
      VAt ctx.Γ ctx.criticalPath.firstStep⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hcyclic)
      le_rfl).trans_eq hlong.2.1
  have hnot : ¬ ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a' := by
    intro hle
    have hcard := hindex
    unfold QuotientCardEq at hcard
    rw [sup_eq_right.mpr hle] at hcard
    have hpositive := Nat.card_pos (α := ZAt ctx.Γ ctx.criticalPath.a')
    omega
  exact ⟨hinvolution, (nine_three_second_extraction_inputs ctx hb).2.2.1,
    hlocal, hnormalizer, le_inf hcommutator hcontain,
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentral, hnot⟩

end Stellmacher.SectionNine
