module

public import CFSG.Quasithin.Chapter4.Defs
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Covering and maximality in general pushing up

Lemma 4.1.3 of Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed p. 606. Covering passes from `I`
through `I₀` to `I₁` by factoring elements twice. A strict increase in the
two-core then excludes all overgroups outside `M` by the definition of `μ*`.
This argument needs neither simplicity nor quasithinness.
-/

public section

namespace CFSG.Quasithin.Chapter4

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- The commutator construction really tests the action on `X/O₂(X)`.
The core is characteristic in `X`; no ambient normality is imposed. -/
theorem le_sectionCentralizer_iff (D X : Subgroup G) :
    D ≤ sectionCentralizer X ↔ D ≤ normalizer (X : Set G) ∧ ⁅D, X⁆ ≤ X.pCoreIn 2 := by
  apply le_commutatorPreimage_iff
  exact normalizer_le_normalizer_characteristic_image X (pCore 2 X)

/-- Lemma 4.1.3(1), with the unused QTKE assumptions omitted. -/
theorem lemma_4_1_3_1 {M Mplus Mminus I I₀ I₁ : Subgroup G}
    (hI : I ∈ eta M Mplus Mminus) (hII₀ : I ≤ I₀) (hI₀ : I₀ ≤ Mminus)
    (hI₁ : I₁ ≤ I₀) (hcore : I₁.pCoreIn 2 ≠ ⊥)
    (hcover : (I₀ : Set G) =
      (I₁ : Set G) * (sectionCentralizerIn I₀ Mplus : Set G))
    (hplus : (Mplus ⊓ I₀ : Set G) ⊆ (I₁ : Set G) * (Mplus.pCoreIn 2 : Set G))
    (hminus : Mminus ≤ M) : I₁ ∈ eta M Mplus Mminus := by
  rcases hI with ⟨hI, hIC, hIP, _⟩
  have hCM : sectionCentralizerIn M Mplus ≤ Mminus := by
    intro c hc
    change c ∈ (Mminus : Set G)
    rw [← hIC]
    exact Set.mem_mul.mpr ⟨1, I.one_mem, c, hc, one_mul c⟩
  refine ⟨hI₁.trans hI₀, ?_, ?_, hcore⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨a, ha, c, hc, rfl⟩
      exact Mminus.mul_mem (hI₀ (hI₁ ha)) (hCM hc)
    · intro x hx
      obtain ⟨i, hi, c, hc, rfl⟩ := Set.mem_mul.mp (hIC.symm ▸ hx)
      have hi₀ : i ∈ (I₀ : Set G) := hII₀ hi
      obtain ⟨j, hj, d, hd, rfl⟩ := Set.mem_mul.mp (hcover ▸ hi₀)
      exact Set.mem_mul.mpr ⟨j, hj, d * c,
        (sectionCentralizerIn M Mplus).mul_mem ⟨hminus (hI₀ hd.1), hd.2⟩ hc,
        (mul_assoc j d c).symm⟩
  · intro x hx
    obtain ⟨i, hi, q, hq, heq⟩ := Set.mem_mul.mp (hIP hx)
    have hip : i ∈ Mplus := by
      have h := Mplus.mul_mem hx (Mplus.inv_mem (pCoreIn_le 2 Mplus hq))
      simpa only [← heq, mul_inv_cancel_right] using h
    obtain ⟨j, hj, r, hr, hji⟩ := Set.mem_mul.mp (hplus ⟨hip, hII₀ hi⟩)
    refine Set.mem_mul.mpr ⟨j, hj, r * q, (Mplus.pCoreIn 2).mul_mem hr hq, ?_⟩
    rw [← mul_assoc, hji, heq]

/-- A strictly larger core above a maximal counterexample cannot have a
nontrivial-core overgroup outside `M`. -/
theorem no_outside_of_muStar {M Mplus Mminus I I₁ : Subgroup G}
    (hI : I ∈ muStar M Mplus Mminus) (hI₁ : I₁ ∈ eta M Mplus Mminus)
    (hrel : PushLE Mplus I I₁) (hlt : I.pCoreIn 2 < I₁.pCoreIn 2) :
    ¬ (Chapter1.HOutside G (I₁ : Set G) (M : Set G)).Nonempty := by
  intro h
  exact hI.2 I₁ ⟨hI₁, h⟩ hrel hlt

/-- Absence of outside overgroups gives literal uniqueness among maximal
two-locals, since every two-local has nontrivial two-core. -/
theorem uniqueMaximalOvergroup_of_no_outside {I M : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hIM : I ≤ M)
    (hno : ¬ (Chapter1.HOutside G (I : Set G) (M : Set G)).Nonempty) :
    UniqueMaximalOvergroup I M := by
  refine ⟨hM, hIM, ?_⟩
  intro N hN hIN
  have hNM : N ≤ M := by
    by_contra h
    exact hno ⟨N, ⟨⟨Chapter1.mem_H_of_isTwoLocal hN.1, hIN⟩, h⟩⟩
  exact hN.eq_of_le hM.1 hNM

/-- Lemma 4.1.3(2). -/
theorem lemma_4_1_3_2 {M Mplus Mminus I I₀ I₁ : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hminus : Mminus ≤ M)
    (hI : I ∈ muStar M Mplus Mminus) (hII₀ : I ≤ I₀) (hI₀ : I₀ ≤ Mminus)
    (hI₁ : I₁ ≤ I₀) (hcore : I₁.pCoreIn 2 ≠ ⊥)
    (hcover : (I₀ : Set G) =
      (I₁ : Set G) * (sectionCentralizerIn I₀ Mplus : Set G))
    (hplus : (Mplus ⊓ I₀ : Set G) ⊆ (I₁ : Set G) * (Mplus.pCoreIn 2 : Set G))
    (hrel : PushLE Mplus I I₁) (hlt : I.pCoreIn 2 < I₁.pCoreIn 2) :
    UniqueMaximalOvergroup I₁ M := by
  have heta := lemma_4_1_3_1 hI.1.1 hII₀ hI₀ hI₁ hcore hcover hplus hminus
  exact uniqueMaximalOvergroup_of_no_outside hM (heta.1.trans hminus)
    (no_outside_of_muStar hI heta hrel hlt)

end CFSG.Quasithin.Chapter4
