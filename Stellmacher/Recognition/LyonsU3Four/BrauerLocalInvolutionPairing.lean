module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveSectionFunctions
public import Theory.Character.InvolutionSum
public import Theory.Character.Inflation

/-!
# The local involution pairing in Lyons's Lemma 4

The local section column is evaluated on the actual centralizer, with the
actual odd core retained as the kernel of the quotient.  Once the involution
sums of the inflated genuine rows have been evaluated by the local fusion
argument, the pairing is a finite character-table calculation.  The signed
section coefficients contribute
`16 * (1 + 2 r)^2 + (4 - 8 r)^2 - 32 = 128 r^2`, where
`r = |C| / |D|`.

The involution-sum hypotheses below are deliberately stated for the actual
class functions on the actual centralizer.  Thus the theorem does not replace
the odd core by a trivial subgroup or identify quotient fibres implicitly.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), p. 381,
Lemma 4(b--c).
-/

public section
noncomputable section
namespace Stellmacher.Recognition.LyonsU3Four

open scoped BigOperators
open Theory.Character
attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G] [Finite G]
variable {S : Sylow 2 G} {α : FiveComplement →* MulAut S}

def inflatedLocalFiveRow
    (T : LocalFiveCharacterTable S α) {H : Type*} [Group H]
    (N : Subgroup H) [N.Normal]
    (e : (H ⧸ N) ≃* LocalFiveGroup S α)
    (i : LocalFiveRowIndex S) : ClassFunction H :=
  fun a => T.row i (ConjClasses.mk (e (QuotientGroup.mk' N a)))

/-- Evaluate an inflated row in the supplied quotient coordinates. -/
@[simp] theorem inflatedLocalFiveRow_apply
    (T : LocalFiveCharacterTable S α) {H : Type*} [Group H]
    (N : Subgroup H) [N.Normal]
    (e : (H ⧸ N) ≃* LocalFiveGroup S α) (i : LocalFiveRowIndex S) (a : H) :
    inflatedLocalFiveRow T N e i a =
      T.row i (ConjClasses.mk (e (QuotientGroup.mk' N a))) := by
  unfold inflatedLocalFiveRow
  rfl

/-- Inflation of every genuine ordinary row remains irreducible. -/
theorem inflatedLocalFiveRow_irreducible
    (T : LocalFiveCharacterTable S α) {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (e : (H ⧸ N) ≃* LocalFiveGroup S α) (i : LocalFiveRowIndex S) :
    IsIrreducibleCharacter (inflatedLocalFiveRow T N e i) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf := isIrreducibleConjCharacter_comp_surjective f
    (e.surjective.comp (QuotientGroup.mk'_surjective N)) (T.row_complete.1 i)
  obtain ⟨n, ρ, hρ⟩ := hf.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hf.2
  · change ofConjClassFunction (T.row i ∘ ConjClasses.map f) = _
    rw [hρ]
    rfl

private theorem inflatedLocalFiveRow_one
    (T : LocalFiveCharacterTable S α) {H : Type*} [Group H]
    (N : Subgroup H) [N.Normal]
    (e : (H ⧸ N) ≃* LocalFiveGroup S α)
    (i : LocalFiveRowIndex S) :
    inflatedLocalFiveRow T N e i 1 = T.row i (ConjClasses.mk 1) := by
  simp [inflatedLocalFiveRow]

private theorem inflated_section_eq_sum
    (T : LocalFiveCharacterTable S α) {H : Type*} [Group H]
    (N : Subgroup H) [N.Normal]
    (e : (H ⧸ N) ≃* LocalFiveGroup S α) (w : QuarticCentralIndex S)
    (j : FiveLinearIndex) :
    T.inflatedSectionClassFunction w N e j =
      ∑ i : LocalFiveRowIndex S,
        (localFiveSectionRow S w i j : ℂ) • inflatedLocalFiveRow T N e i := by
  classical
  funext a
  change T.sectionClassFunction w j (e (QuotientGroup.mk' N a)) = _
  rw [T.sectionClassFunction_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, inflatedLocalFiveRow]
  apply Finset.sum_congr
  · ext i; simp
  · intro i _; rfl

theorem brauerLocalInvolutionPairing_of_actual_sums
    (T : LocalFiveCharacterTable S α) (w : QuarticCentralIndex S)
    (h : SylowStructure S)
    {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (e : (H ⧸ N) ≃* LocalFiveGroup S α)
    (D : Subgroup H) (r : ℂ)
    (hr : (Nat.card H : ℂ) = r * (Nat.card D : ℂ))
    (j : FiveLinearIndex)
    (hχ : ∀ i, IsIrreducibleCharacter (inflatedLocalFiveRow T N e i))
    (hlin : ∀ χ : FiveLinearIndex,
      involutionSum (inflatedLocalFiveRow T N e (.inl χ)) = 1 + 2 * r)
    (hquartic : ∀ z : QuarticCentralIndex S, ∀ χ : FiveLinearIndex,
      involutionSum (inflatedLocalFiveRow T N e (.inr (.inl (z, χ)))) =
        if z = w then 4 - 8 * r else -4)
    (hquintic : ∀ i : Fin 3,
      involutionSum (inflatedLocalFiveRow T N e (.inr (.inr i))) = 5 + 10 * r) :
    (Nat.card D : ℂ)^2 *
        scalarProduct H (T.inflatedSectionClassFunction w N e j)
          (fun a => (involutionPairCount a : ℂ)) =
      128 * (Nat.card H : ℂ) := by
  classical
  let R : LocalFiveRowIndex S → ClassFunction H :=
    inflatedLocalFiveRow T N e
  have hRone (i : LocalFiveRowIndex S) : R i 1 =
      (localFiveRowDegree S i : ℂ) := by
    rw [show R i = inflatedLocalFiveRow T N e i from rfl,
      inflatedLocalFiveRow_one]
    exact T.row_degree i
  have hΦ : T.inflatedSectionClassFunction w N e j =
      ∑ i : LocalFiveRowIndex S,
        (localFiveSectionRow S w i j : ℂ) • R i := by
    exact inflated_section_eq_sum T N e w j
  rw [hΦ, scalarProduct_expansion_involutionPairCount R hχ]
  have hlinR : ∀ χ : FiveLinearIndex,
      involutionSum (R (.inl χ)) = 1 + 2 * r := by
    intro χ
    exact hlin χ
  have hquarticR : ∀ z : QuarticCentralIndex S, ∀ χ : FiveLinearIndex,
      involutionSum (R (.inr (.inl (z, χ)))) =
        if z = w then 4 - 8 * r else -4 := by
    intro z χ
    exact hquartic z χ
  have hquinticR : ∀ i : Fin 3,
      involutionSum (R (.inr (.inr i))) = 5 + 10 * r := by
    intro i
    exact hquintic i
  have hz : Nat.card (QuarticCentralIndex S) = 3 := quarticCentralIndex_card S h
  have hc : Nat.card FiveLinearIndex = 5 := fiveLinearIndex_card
  have hcalc :
      ∑ i : LocalFiveRowIndex S,
        involutionSum (R i) ^ 2 * (localFiveSectionRow S w i j : ℂ) / R i 1 =
      16 * (1 + 2 * r)^2 + (4 - 8 * r)^2 - 32 := by
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [hRone, hlinR, hquarticR, hquinticR, localFiveSectionRow,
      localFiveRowDegree, Sum.elim_inl, Sum.elim_inr, Int.cast_mul,
      Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_neg,
      Nat.cast_one, Nat.cast_ofNat]
    have hinner (z : QuarticCentralIndex S) :
        (∑ χ : FiveLinearIndex, (if z = w then 4 - 8 * r else -4)^2 *
          ((if z = w then (1 : ℂ) else -1) * (if χ = j then 0 else 1)) / 4) =
            if z = w then (4 - 8 * r)^2 else -16 := by
      by_cases hzw : z = w
      · simp only [hzw, if_true, mul_ite, mul_zero, mul_one,
          ite_div, zero_div]
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
          Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ]
        rw [show Fintype.card FiveLinearIndex = 5 by
          rw [← Nat.card_eq_fintype_card, hc]]
        norm_num
        ring
      · simp only [hzw, if_false, mul_ite, mul_zero, mul_one,
          ite_div, zero_div]
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
          Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ]
        rw [show Fintype.card FiveLinearIndex = 5 by
          rw [← Nat.card_eq_fintype_card, hc]]
        norm_num
    simp_rw [hinner]
    simp only [div_one, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
      show (Finset.univ.filter (fun z : QuarticCentralIndex S => z = w)).card = 1 by
        rw [Finset.filter_eq']; simp,
      Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ w),
      Finset.card_univ,
      show Fintype.card (QuarticCentralIndex S) = 3 by rw [← Nat.card_eq_fintype_card, hz]]
    norm_num
    ring

  rw [hcalc]
  have hH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hD : (Nat.card D : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := D)).ne'
  rw [show 16 * (1 + 2 * r)^2 + (4 - 8 * r)^2 - 32 = 128 * r^2 by ring]
  rw [hr]
  field_simp

end Stellmacher.Recognition.LyonsU3Four
