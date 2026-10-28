module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.Character.IrreducibleDegrees
public import Theory.Character.InvolutionSum

/-!
# Reductions using Suzuki's involution-pair identity

A character expansion paired with actual involution products gives the ambient
order factor `|G| / 384²`, since the involutions form one conjugacy class and
have centralizer order 384. Once the separate local pairings are evaluated,
this proves all five Suzuki identities. Their evaluation is an explicit premise
here, rather than an asserted order theorem.

The fifth identity rules out any expansion with at most two irreducibles:
vanishing at 1 and z makes the degree expression zero, while its computed
pairing must be -5. The elementary cofactor estimate retains the endpoint 55.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 11, pp.12–13, and the order estimate on p.15;
Suzuki's involution-pair formula is derived through the existing ordinary
character expansion, not assumed as an order-recognition theorem.
-/

open scoped BigOperators
open Subgroup
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
variable {G : Type*} [Group G] [Finite G]

/-- Suzuki's identity for any supplied finite irreducible expansion of one
of the five actual induced characters. -/
public theorem suzukiOrder_identity (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    {J : Type*} [Fintype J] (χ : J → ClassFunction G)
    (hχ : ∀ j, IsIrreducibleCharacter (χ j)) (a : J → ℂ) (i : Fin 5)
    (he : I.induced i = ∑ j, a j • χ j) :
    (Nat.card G : ℂ) / 147456 * ∑ j, a j * χ j D.z ^ 2 / χ j 1 =
      (pairingConstants i : ℂ) := by
  have hf (j) : IsClassFunction (χ j) := by
    obtain ⟨n, ρ, _, hr⟩ := hχ j
    rw [hr]
    exact ρ.char_conj
  have hh := hI i
  rw [he, Theory.Character.scalarProduct_expansion_involutionPairCount χ hχ a] at hh
  simp_rw [Theory.Character.involutionSum_of_fusion D.z D.z_order
    L.involution_fusion _ (hf _), D.centralizer_card] at hh
  rw [Finset.mul_sum] at hh ⊢
  have hg : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  convert hh using 1
  apply Finset.sum_congr rfl
  intro j _
  field_simp
  ring

/-- The strict small-ratio estimate permits h = 55. -/
public theorem cofactor_le55_of_suzuki_sum (g h : ℕ) (s : ℚ) (hs : (1 / 2 : ℚ) < s)
    (horder : g = 40320 * h)
    (heq : (g : ℚ) / 147456 * s = 91 / 12) : h ≤ 55 := by
  have hg : (0 : ℚ) ≤ g := Nat.cast_nonneg g
  have hb : (g : ℚ) < 2236416 := by nlinarith
  have hb' : g < 2236416 := by exact_mod_cast hb
  omega

private theorem two_term_cancellation (a b x y t u : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hdeg : a * x + b * y = 0) (hval : a * t + b * u = 0) :
    a * t ^ 2 / x + b * u ^ 2 / y = 0 := by
  by_cases hb : b = 0
  · have ha : a = 0 := (mul_eq_zero.mp (by simpa [hb] using hdeg)).resolve_right hx
    simp [ha, hb]
  have hby : b * y = -a * x := by linear_combination hdeg
  have hbu : b * u = -a * t := by linear_combination hval
  have hc : b * (a * t ^ 2 * y + b * u ^ 2 * x) = 0 := by
    calc
      _ = a * t ^ 2 * (b * y) + (b * u) ^ 2 * x := by ring
      _ = 0 := by rw [hby, hbu]; ring
  have hn := (mul_eq_zero.mp hc).resolve_left hb
  field_simp
  linear_combination hn

/-- The fifth exceptional induction cannot be supported on only two
irreducible characters. This excludes its norm-five pattern with multiplicities
one and two in Lemma 11. -/
public theorem fifth_induction_ne_two_irreducibles (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (χ η : ClassFunction G) (hχ : IsIrreducibleCharacter χ)
    (hη : IsIrreducibleCharacter η) (a b : ℂ) :
    I.induced 4 ≠ a • χ + b • η := by
  intro he
  have h1 : a * χ 1 + b * η 1 = 0 := by
    have hh := I.degree_zero 4
    change I.induced 4 1 = 0 at hh
    simpa only [he, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
  have hv : I.induced 4 D.z = 0 := by
    simpa [SpecialInductionData.induced, specialRepresentative, exceptionalValues,
      CaseII.into_z_zero] using I.values 4 0
  have hz : a * χ D.z + b * η D.z = 0 := by
    simpa only [he, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hv
  have hc : χ 1 ≠ 0 := by rw [hχ.degree_eq]; exact_mod_cast hχ.degree_pos.ne'
  have hd : η 1 ≠ 0 := by rw [hη.degree_eq]; exact_mod_cast hη.degree_pos.ne'
  have hzero := two_term_cancellation a b (χ 1) (η 1) (χ D.z) (η D.z) hc hd h1 hz
  have hfamily : ∀ r : Fin 2, IsIrreducibleCharacter (![χ, η] r) := by
    intro r
    fin_cases r
    · exact hχ
    · exact hη
  have hh := suzukiOrder_identity D k L I hI ![χ, η] hfamily ![a, b] 4
    (by simpa [Fin.sum_univ_two] using he)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    hzero, mul_zero] at hh
  change (0 : ℂ) = ((-5 : ℚ) : ℂ) at hh
  norm_num at hh
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
