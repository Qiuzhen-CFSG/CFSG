module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.Construction

/-!
# The order-eight column of the induced normalizer characters

Every element of order eight in the marked centralizer has fourth power z₁.
This is checked on its seventeen already classified local representatives and
transported by conjugacy. Consequently any normalizer element carrying the
marked order-eight element back into the inertia subgroup centralizes z₁ and
itself lies in that subgroup. The induction sum therefore equals the original
inertia character value, which gives the source column 1,-1,0,1,-1.

Together with the degrees, this column proves that the five actual induced
characters are distinct. Irreducibility and the other seven unproved columns
are not asserted here.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 5–6, pp.9–11.
-/

open Subgroup
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy CaseII
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
private theorem eight_root (t : TwistedModel) (h8 : t ^ 8 = 1) (h4 : t ^ 4 ≠ 1) :
    t ^ 4 = z 0 := by
  have hc := Distribution.localClass_conjugate t
  have h8rep : Distribution.localRepresentative (Distribution.localClass t) ^ 8 = 1 := by
    simpa only [h8, isConj_one_right] using hc.pow 8
  have h4rep : Distribution.localRepresentative (Distribution.localClass t) ^ 4 ≠ 1 := by
    intro he
    have hh := hc.pow 4
    rw [he, isConj_one_left] at hh
    exact h4 hh
  have hsmall : ∀ i : Fin 17, Distribution.localRepresentative i ^ 8 = 1 →
      Distribution.localRepresentative i ^ 4 ≠ 1 →
      Distribution.localRepresentative i ^ 4 = z 0 := by decide +kernel
  have hz := hc.pow 4
  rw [hsmall _ h8rep h4rep] at hz
  obtain ⟨g, hg⟩ := isConj_iff.mp hz.symm
  rw [(z_zero_mem_center.comm g).eq.symm, mul_inv_cancel_right] at hg
  exact hg.symm
private theorem marked_eight_root : (z 1 * b * d) ^ 4 = z 0 := by decide +kernel
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
include L in
private theorem inertia_mem (x : normalizer (E D k : Set G)) :
    x ∈ normalizerInertia D k ↔ (x : G) ∈ D.centralizer := by
  rw [normalizerInertia_eq_range D k L]
  constructor
  · rintro ⟨t, rfl⟩
    exact (k t).property
  · intro hx
    obtain ⟨t, ht⟩ := k.surjective ⟨x, hx⟩
    exact ⟨t, Subtype.ext (congrArg (fun y : D.centralizer => (y : G)) ht)⟩
include L in
private theorem eight_transport (x : normalizer (E D k : Set G))
    (hx : x⁻¹ * normalizerCentralizer D k (z 1 * b * d) * x ∈ normalizerInertia D k) :
    x ∈ normalizerInertia D k := by
  rw [normalizerInertia_eq_range D k L] at hx
  obtain ⟨t, ht⟩ := hx
  have hp (m : ℕ) : (x⁻¹ * normalizerCentralizer D k (z 1 * b * d) * x) ^ m =
      x⁻¹ * normalizerCentralizer D k (z 1 * b * d) ^ m * x := by
    simpa only [inv_inv] using (conj_pow (i := m) (a := x⁻¹)
      (b := normalizerCentralizer D k (z 1 * b * d)))
  have h4 : normalizerCentralizer D k (t ^ 4) =
      x⁻¹ * normalizerCentralizer D k (z 0) * x := by
    rw [map_pow, ht, hp, ← map_pow, marked_eight_root]
  have ht8 : t ^ 8 = 1 := by
    apply normalizerCentralizer_injective D k
    have hh : (z 1 * b * d) ^ 8 = 1 := by decide +kernel
    rw [map_pow, ht, hp, ← map_pow, hh, map_one, mul_one, inv_mul_cancel]
  have ht4 : t ^ 4 ≠ 1 := by
    intro he
    have hz : normalizerCentralizer D k (z 0) = 1 := by
      have hh := congrArg (fun y => x * y * x⁻¹) h4
      simpa [he, mul_assoc] using hh.symm
    have hz0 : z 0 = 1 := normalizerCentralizer_injective D k (hz.trans (map_one _).symm)
    exact (by decide +kernel : z 0 ≠ 1) hz0
  rw [eight_root t ht8 ht4] at h4
  apply (inertia_mem D k L x).mpr
  apply mem_centralizer_singleton_iff.mpr
  have hg : D.z = (x : G)⁻¹ * D.z * x := by
    have hh : into D k (z 0) = (x : G)⁻¹ * into D k (z 0) * x :=
      congrArg (fun y : normalizer (E D k : Set G) => (y : G)) h4
    simpa only [into_z_zero] using hh
  calc
    (x : G) * D.z = (x : G) * ((x : G)⁻¹ * D.z * x) := congrArg ((x : G) * ·) hg
    _ = D.z * x := by group

private theorem induction_value {H : Type*} [Group H] [Finite H] (I : Subgroup H)
    (φ : ClassFunction I) (hc : IsClassFunction φ) (a : I)
    (htrans : ∀ g : H, g⁻¹ * (a : H) * g ∈ I → g ∈ I) :
    inducedClassFunction I φ a = φ a := by
  classical
  unfold inducedClassFunction
  have hs : (∑ g : H, if h : g⁻¹ * (a : H) * g ∈ I then φ ⟨_, h⟩ else 0) =
      ∑ _g : I, φ a := by
    apply Finset.sum_congr_set (I : Set H)
    · intro g hg
      have hm := I.mul_mem (I.mul_mem (I.inv_mem hg) a.property) hg
      rw [dif_pos hm]
      have he : (⟨g⁻¹ * (a : H) * g, hm⟩ : I) =
          (⟨g, hg⟩ : I)⁻¹ * a * ⟨g, hg⟩ := Subtype.ext rfl
      rw [he]
      simpa only [inv_inv] using hc a (⟨g, hg⟩ : I)⁻¹
    · intro g hg
      exact dif_neg (fun hm => hg (htrans g hm))
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [inv_mul_cancel_left₀]
  exact_mod_cast Nat.card_pos (α := I) |>.ne'

/-- The actual induced values at the marked order-eight element z₂bd. -/
public theorem normalizerInducedCharacter_eight (j : Fin 5) :
    normalizerInducedCharacter D k L j (normalizerCentralizer D k (z 1 * b * d)) =
      (![1, -1, 0, 1, -1] j : ℂ) := by
  have hc : IsClassFunction (normalizerInertiaCharacter D k L j) := by
    obtain ⟨n, ρ, _, he⟩ := normalizerInertiaCharacter_irreducible D k L j
    rw [he]
    exact fun x g => Representation.char_conj ρ x g
  have hv := induction_value (normalizerInertia D k) (normalizerInertiaCharacter D k L j) hc
    (normalizerInertiaEquiv D k L (z 1 * b * d)) (eight_transport D k L)
  change normalizerInducedCharacter D k L j (normalizerCentralizer D k (z 1 * b * d)) = _ at hv
  rw [hv, normalizerInertiaCharacter_apply]
  change (binaryParitySign (z 1 * b * d).left : ℂ) *
    (SymmetricFourCharacters.table (normalizerInertiaCharacterIndex j)
      (SymmetricFourClasses.classIndex (z 1 * b * d).right) : ℂ) = _
  rw [← Int.cast_mul]
  have ht : ∀ j : Fin 5, binaryParitySign (z 1 * b * d).left *
      SymmetricFourCharacters.table (normalizerInertiaCharacterIndex j)
        (SymmetricFourClasses.classIndex (z 1 * b * d).right) = (![1, -1, 0, 1, -1] j : ℤ) := by
    decide +kernel
  rw [ht]
  fin_cases j <;> norm_num

/-- The order-eight values are the prescribed third special column. -/
public theorem normalizerInducedCharacter_eight_values (Q : NormalizerClassData D k)
    (j : Fin 5) :
    normalizerInducedCharacter D k L j (Q.representative 2) =
      normalizerFullValues 0 (Fin.natAdd 7 j) 2 := by
  change normalizerInducedCharacter D k L j (normalizerCentralizer D k (z 1 * b * d)) =
    (normalizerCharacterValues (Fin.natAdd 7 j) 2 : ℂ)
  rw [normalizerInducedCharacter_eight]
  have ht : ∀ j : Fin 5, normalizerCharacterValues (Fin.natAdd 7 j) 2 =
      (![1, -1, 0, 1, -1] j : ℤ) := by decide +kernel
  rw [ht]
  fin_cases j <;> norm_num

/-- The degrees and the order-eight values distinguish the five constructed characters. -/
public theorem normalizerInducedCharacter_injective :
    Function.Injective (normalizerInducedCharacter D k L) := by
  intro i j hij
  have hdegree := congrFun hij 1
  rw [normalizerInducedCharacter_one, normalizerInducedCharacter_one] at hdegree
  have height := congrFun hij (normalizerCentralizer D k (z 1 * b * d))
  rw [normalizerInducedCharacter_eight, normalizerInducedCharacter_eight] at height
  fin_cases i <;> fin_cases j <;> norm_num at *

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
