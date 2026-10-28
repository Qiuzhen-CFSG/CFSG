module

public import Stellmacher.Recognition.LyonsU3Four.BrauerLocalInvolutionClasses
public import Stellmacher.Recognition.LyonsU3Four.BrauerLocalInvolutionPairing
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveRestrictionSums
/-!
# Evaluation of the actual local involution pairing

Apply the three-class formula in `BrauerLocalInvolutionClasses` to the genuine
ordinary rows inflated through the actual odd core. Their already proved
central averages and central values give the linear, quartic and quintic
involution sums. In particular a quartic with a different central kernel has
value minus four at `z`, and opposite values on the other two representatives.

The signed local section expansion then evaluates the involution-pair pairing
as `128 * |C_G(z)| / |C_G(Z(S))|²`. Every class count and every row sum is
proved; the quotient equivalence only specifies the actual local coordinates.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 381,
Lemma 4(b–c).
-/

public section
open scoped BigOperators
open Subgroup Theory.Character
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Stellmacher.Recognition.LyonsU3Four
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    {α : FiveComplement →* MulAut S}
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    {z : G} (hz : z ∈ centerImage S)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (T : LocalFiveCharacterTable S α)

include h β hβ hα hz he hw

private theorem row_involutionSum (i : LocalFiveRowIndex S) :
    involutionSum (inflatedLocalFiveRow T (pPrimeCore 2 _) e i) =
      T.row i (ConjClasses.mk (SemidirectProduct.inl w.1.1)) +
        ((Nat.card (centralizer ({z} : Set G)) : ℂ) /
          Nat.card (centralizer (centerImage S : Set G))) *
        ((match i with | .inl _ => (4 : ℂ) | .inr (.inl _) => 0 | .inr (.inr _) => 20) -
          (localFiveRowDegree S i : ℂ) - T.row i (ConjClasses.mk (SemidirectProduct.inl w.1.1))) := by
  have hf : IsClassFunction (inflatedLocalFiveRow T (pPrimeCore 2 _) e i) := by
    obtain ⟨n, ρ, _, hρ⟩ := inflatedLocalFiveRow_irreducible T (pPrimeCore 2 _) e i
    rw [hρ]
    exact Representation.char_conj ρ
  rw [local_involutionSum h β hβ hα hz e he w hw _ hf]
  have hv (v : center S) :
      inflatedLocalFiveRow T (pPrimeCore 2 _) e i
        (inclusion (sylow_le_involutionCentralizer S hz) v.val) =
      T.row i (ConjClasses.mk (SemidirectProduct.inl v.val)) := by
    rw [inflatedLocalFiveRow_apply]
    change T.row i (ConjClasses.mk (e (involutionCentralizerQuotientMap S hz v.val))) = _
    rw [he]
  have hv1 : inflatedLocalFiveRow T (pPrimeCore 2 _) e i 1 =
      (localFiveRowDegree S i : ℂ) := by
    simp only [inflatedLocalFiveRow_apply, map_one, T.row_degree]
  simp_rw [hv, hv1]
  rw [T.sum_center h]
  rcases i with χ | (⟨v, χ⟩ | i) <;> rfl

/-- The actual involution sum of every inflated linear row. -/
theorem inflatedLocalFiveRow_involutionSum_linear (χ : FiveLinearIndex) :
    involutionSum (inflatedLocalFiveRow T (pPrimeCore 2 _) e (.inl χ)) =
      1 + 2 * ((Nat.card (centralizer ({z} : Set G)) : ℂ) /
        Nat.card (centralizer (centerImage S : Set G))) := by
  rw [row_involutionSum h β hβ hα hz e he w hw T]
  simp only [T.linear_value, SemidirectProduct.right_inl, map_one,
    localFiveRowDegree, Sum.elim_inl, Nat.cast_one]
  ring

/-- The quartic with central kernel `z` has sum `4 - 8 r`; each other quartic
has sum `-4`, since its two remaining central values cancel. -/
theorem inflatedLocalFiveRow_involutionSum_quartic
    (v : QuarticCentralIndex S) (χ : FiveLinearIndex) :
    involutionSum (inflatedLocalFiveRow T (pPrimeCore 2 _) e (.inr (.inl (v, χ)))) =
      if v = w then 4 - 8 * ((Nat.card (centralizer ({z} : Set G)) : ℂ) /
        Nat.card (centralizer (centerImage S : Set G))) else -4 := by
  rw [row_involutionSum h β hβ hα hz e he w hw T]
  have hw1 : w.1.1 ≠ (1 : S) := fun hh => w.property (Subtype.ext hh)
  have hwv : w.1.1 = v.1.1 ↔ v = w := by
    constructor
    · intro hh; exact (Subtype.ext (Subtype.ext hh)).symm
    · rintro rfl; rfl
  simp only [T.quartic_restriction, hw1, false_or, hwv, w.1.property, if_true,
    localFiveRowDegree, Sum.elim_inr, Sum.elim_inl, Nat.cast_ofNat]
  split_ifs <;> ring

/-- The actual involution sum of each inflated quintic row. -/
theorem inflatedLocalFiveRow_involutionSum_quintic (i : Fin 3) :
    involutionSum (inflatedLocalFiveRow T (pPrimeCore 2 _) e (.inr (.inr i))) =
      5 + 10 * ((Nat.card (centralizer ({z} : Set G)) : ℂ) /
        Nat.card (centralizer (centerImage S : Set G))) := by
  rw [row_involutionSum h β hβ hα hz e he w hw T]
  have hv : T.row (.inr (.inr i)) (ConjClasses.mk (SemidirectProduct.inl w.1.1)) = 5 :=
    localFiveQuintic_central_value S α h (T.quinticSeed i) w.val
  rw [hv]
  simp only [localFiveRowDegree, Sum.elim_inr, Nat.cast_ofNat]
  ring

/-- The genuine local pairing, retaining the actual odd core and actual
centralizer orders. All row sums are discharged by local conjugacy counting. -/
theorem brauerLocalInvolutionPairing (j : FiveLinearIndex) :
    (Nat.card (centralizer (centerImage S : Set G)) : ℂ)^2 *
      scalarProduct (centralizer ({z} : Set G))
        (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e j)
        (fun a => (involutionPairCount a : ℂ)) =
      128 * (Nat.card (centralizer ({z} : Set G)) : ℂ) := by
  let C := centralizer ({z} : Set G)
  let D := centralizer (centerImage S : Set G)
  have hD : Nat.card (D.subgroupOf C) = Nat.card D :=
    Nat.card_congr (subgroupOfEquivOfLe (centralizer_le (Set.singleton_subset_iff.mpr hz))).toEquiv
  have hDn : (Nat.card D : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := D)).ne'
  have hp := brauerLocalInvolutionPairing_of_actual_sums T w h (pPrimeCore 2 C) e
    (D.subgroupOf C) ((Nat.card C : ℂ) / Nat.card D)
    (by rw [hD]; exact (div_mul_cancel₀ _ hDn).symm) j
    (inflatedLocalFiveRow_irreducible T (pPrimeCore 2 C) e)
    (inflatedLocalFiveRow_involutionSum_linear h β hβ hα hz e he w hw T)
    (inflatedLocalFiveRow_involutionSum_quartic h β hβ hα hz e he w hw T)
    (inflatedLocalFiveRow_involutionSum_quintic h β hβ hα hz e he w hw T)
  rw [hD] at hp
  convert hp using 1
  congr
  exact Subsingleton.elim _ _

end Stellmacher.Recognition.LyonsU3Four
