module

public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Theory.GroupTheory.PResidual.NormalizedGenerators
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Constructing the component and its conjugation action

Trivial odd core gives `F(I) = O₂(I)`. Thus `F*(I) ≠ O₂(I)` forces the
component layer to contain a component. The normalizer action, restricted to
`Z`, is faithful whenever the supplied 1.1.5 centralizer conclusion has trivial
kernel. Its evaluation is conjugation in the same ambient group.

If the component contains the two normalized, two-perfect factors, their
join is `O²(I)`. Perfectness of the component gives the opposite inclusion,
identifying it with both the residual and the factor join. This step uses the
proved universal property of the residual and has no classification assumption.

Model elimination, the containment of the factors, and the local centralizer
index remain separate obligations. Nothing here identifies `I/O_{3'}(I)`
with a quotient by the three-prime residual.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of 15.4.18, printed pp.1162–1163, and F.6.6.
-/

@[expose] public section

open Subgroup
open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch

/-- With trivial odd core, a generalized Fitting subgroup larger than the
two-core contains a component. -/
theorem exists_component_of_generalizedFitting_ne
    {I : Type*} [Group I] [Finite I] (hodd : pPrimeCore 2 I = ⊥)
    (hne : generalizedFitting I ≠ pCore 2 I) :
    ∃ L : Subgroup I, IsComponent I L := by
  by_contra h
  have hn : ∀ L : Subgroup I, ¬ IsComponent I L := by simpa using h
  have hl : componentLayer I = ⊥ := by
    apply le_bot_iff.mp
    exact sSup_le fun L hL => (hn L hL).elim
  exact hne (by rw [generalizedFitting, hl, sup_bot_eq, Fitting_eq_pcore I 2 hodd])

/-- The centralizer condition in 1.1.5 gives an actual faithful conjugation
homomorphism, with its evaluation on every element of the component. -/
theorem exists_faithful_conjugation
    {I : Type*} [Group I] (L Z : Subgroup I)
    (hn : Z ≤ normalizer (L : Set I)) (hc : Z ⊓ centralizer (L : Set I) = ⊥) :
    ∃ ρ : Z →* MulAut L, Function.Injective ρ ∧
      ∀ z : Z, ∀ l : L, (ρ z l : I) = (z : I) * l * (z : I)⁻¹ := by
  let ρ := L.normalizerMonoidHom.comp (inclusion hn)
  refine ⟨ρ, ?_, fun _ _ => rfl⟩
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply le_bot_iff.mp
  intro z hz
  have hnker : inclusion hn z ∈ L.normalizerMonoidHom.ker := hz
  rw [normalizerMonoidHom_ker] at hnker
  have hzc : (z : I) ∈ centralizer (L : Set I) := hnker
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hc ▸
    (show (z : I) ∈ Z ⊓ centralizer (L : Set I) from ⟨z.property, hzc⟩))))

/-- Construct the component and its faithful action from the raw 1.1.5
centralizer conclusions. No model identification is assumed. -/
theorem exists_component_with_faithful_action
    {I : Type*} [Group I] [Finite I] (Z : Subgroup I)
    (hodd : pPrimeCore 2 I = ⊥) (hne : generalizedFitting I ≠ pCore 2 I)
    (h115 : ∀ L : Subgroup I, IsComponent I L →
      Z ≤ normalizer (L : Set I) ∧ Z ⊓ centralizer (L : Set I) = ⊥) :
    ∃ L : Subgroup I, IsComponent I L ∧ ∃ ρ : Z →* MulAut L,
      Function.Injective ρ ∧
      ∀ z : Z, ∀ l : L, (ρ z l : I) = (z : I) * l * (z : I)⁻¹ := by
  obtain ⟨L, hL⟩ := exists_component_of_generalizedFitting_ne hodd hne
  exact ⟨L, hL, exists_faithful_conjugation L Z (h115 L hL).1 (h115 L hL).2⟩

/-- Once both local factors lie in the component, their normalized
factorization identifies the component with the two-residual. This is the
residual step in 15.4.18; it does not replace `O^{3'}` by `O_{3'}`. -/
theorem component_eq_twoResidual_of_factor_containment
    {I : Type*} [Group I] [Finite I] (L Y₁ Y₂ Tᵢ : Subgroup I)
    (hL : IsComponent I L) (h₁ : IsPPerfect 2 Y₁) (h₂ : IsPPerfect 2 Y₂)
    (hT : IsPGroup 2 Tᵢ)
    (hn₁ : Tᵢ ≤ normalizer (Y₁ : Set I)) (hn₂ : Tᵢ ≤ normalizer (Y₂ : Set I))
    (hgen : (Y₁ ⊔ Y₂) ⊔ Tᵢ = ⊤) (hY₁L : Y₁ ≤ L) (hY₂L : Y₂ ≤ L) :
    L = pResidual 2 I ∧ L = Y₁ ⊔ Y₂ := by
  let : IsQuasisimple L := hL.2
  have hr : pResidual 2 I = Y₁ ⊔ Y₂ :=
    pResidual_eq_sup_of_normalized_generators Y₁ Y₂ Tᵢ h₁ h₂ hT hn₁ hn₂ hgen
  have hl : L ≤ pResidual 2 I := by
    apply le_sInf
    rintro N ⟨hN, hp⟩
    let : N.Normal := hN
    let : Group.IsNilpotent (I ⧸ N) := hp.isNilpotent
    exact le_of_isPerfect_of_solvable_quotient L N
  have he : L = pResidual 2 I := le_antisymm hl (hr ▸ sup_le hY₁L hY₂L)
  exact ⟨he, he.trans hr⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
