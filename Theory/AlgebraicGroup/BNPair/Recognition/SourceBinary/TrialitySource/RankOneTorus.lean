module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.WeylPinning

/-!
# The source rank-one torus words

The parameterized three-root word in SL₂ is its literal diagonal matrix
times the Weyl matrix. Apply the two original rank-one maps and the proved
longest-word sign change from WeylPinning. This identifies all nₐ(t), nᵦ(u),
hₐ(t), and hᵦ(u) with the same source matrices. Multiplicativity and the two
rank-one Weyl inversion relations follow before any model comparison.

The units are transported by the original extension equivalence and its
restriction to the actual fixed field. These formulas include q=2.
Cross-torus commutation, mixed characters and the two cross-Weyl actions
still require the source module and full Cartan calculations.
Source: Fong--Seitz II §7 and (9.31); GLS3 2.3.5.
-/

@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Theory.PSL2.SemilinearCoverage
open Triality.Standard Triality.Standard.RootPresentationRecognition
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y] {σ : F ≃+* F}

/-- The parameterized word in the same SL₂ pinning is its diagonal times Weyl. -/
theorem weyl_parameter_word (t : Fˣ) :
    uni t.val * (weyl F * uni (t⁻¹).val * (weyl F)⁻¹) * uni t.val =
      tor t * weyl F := by
  have hw : (weyl F)⁻¹ = weyl F := inv_eq_of_mul_eq_one_right weyl_sq
  rw [hw]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
/-- Multiplication of the actual diagonal matrices. -/
theorem tor_mul (t u : Fˣ) : tor (t*u) = tor t * tor u := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- The source diagonal is a homomorphism before any model comparison. -/
def torHom : Fˣ →* SL2 F where
  toFun := tor
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := tor_mul

/-- Weyl inverts the same diagonal subgroup. -/
theorem weyl_tor (t : Fˣ) : weyl F * tor t * (weyl F)⁻¹ = tor t⁻¹ := by
  have hw : (weyl F)⁻¹ = weyl F := inv_eq_of_mul_eq_one_right weyl_sq
  rw [hw]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

namespace RankOnePair
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
variable (p : RankOnePair σ Y) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ)

theorem nA_parameter (t : Fˣ) :
    (p.signedRoots e).nA (Units.map e.extension.toMonoidHom t) =
      p.shortMap (tor t * weyl F) := by
  have hp (x : F) : (p.signedRoots e).shortValue 0 (e.extension x) = p.s 0 x := by
    simpa [SignedRoots.shortSigned, signedValue] using p.signedRoots_short e true 0 x
  have hn (x : F) : (p.signedRoots e).negativeShortValue 0 (e.extension x) =
      p.dihedral.A (p.s 0 x) := by
    rw [← p.W_shortBase]
    simpa [SignedRoots.shortSigned, signedValue] using p.signedRoots_short e false 0 x
  simp only [SignedRoots.nA, ← map_inv, Units.coe_map]
  change (p.signedRoots e).shortValue 0 (e.extension t.val) *
    (p.signedRoots e).negativeShortValue 0 (e.extension (t⁻¹).val) *
      (p.signedRoots e).shortValue 0 (e.extension t.val) = _
  rw [hp, hn]
  change p.shortMap (uni t.val) *
    (p.shortMap (weyl F) * p.shortMap (uni (t⁻¹).val) * (p.shortMap (weyl F))⁻¹) *
      p.shortMap (uni t.val) = p.shortMap (tor t * weyl F)
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, weyl_parameter_word]

theorem nB_parameter (t : Kˣ) :
    (p.signedRoots e).nB (Units.map e.fixed.toMonoidHom t) =
      p.longMap (tor t * weyl K) := by
  have hp (x : K) : (p.signedRoots e).longValue 0 (e.fixed x) = p.l 0 x := by
    simpa [SignedRoots.longSigned, signedValue] using p.signedRoots_long e true 0 x
  have hn (x : K) : (p.signedRoots e).negativeLongValue 0 (e.fixed x) =
      p.dihedral.B (p.l 0 x) := by
    rw [← p.W_longBase]
    simpa [SignedRoots.longSigned, signedValue] using p.signedRoots_long e false 0 x
  simp only [SignedRoots.nB, ← map_inv, Units.coe_map]
  change (p.signedRoots e).longValue 0 (e.fixed t.val) *
    (p.signedRoots e).negativeLongValue 0 (e.fixed (t⁻¹).val) *
      (p.signedRoots e).longValue 0 (e.fixed t.val) = _
  rw [hp, hn]
  change p.longMap (uni t.val) *
    (p.longMap (weyl K) * p.longMap (uni (t⁻¹).val) * (p.longMap (weyl K))⁻¹) *
      p.longMap (uni t.val) = p.longMap (tor t * weyl K)
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, weyl_parameter_word]

theorem hA_parameter (t : Fˣ) :
    (p.signedRoots e).hA (Units.map e.extension.toMonoidHom t) = p.shortMap (tor t) := by
  rw [SignedRoots.hA, p.nA_parameter, p.nA_one]
  change p.shortMap (tor t * weyl F) * p.shortMap (weyl F) = _
  rw [← map_mul, mul_assoc, weyl_sq, mul_one]

theorem hB_parameter (t : Kˣ) :
    (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t) = p.longMap (tor t) := by
  rw [SignedRoots.hB, p.nB_parameter, p.nB_one]
  change p.longMap (tor t * weyl K) * p.longMap (weyl K) = _
  rw [← map_mul, mul_assoc, weyl_sq, mul_one]

theorem hA_mul (t u : Fˣ) :
    (p.signedRoots e).hA (Units.map e.extension.toMonoidHom (t*u)) =
      (p.signedRoots e).hA (Units.map e.extension.toMonoidHom t) *
        (p.signedRoots e).hA (Units.map e.extension.toMonoidHom u) := by
  rw [p.hA_parameter, p.hA_parameter, p.hA_parameter, tor_mul, map_mul]

theorem hB_mul (t u : Kˣ) :
    (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom (t*u)) =
      (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t) *
        (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom u) := by
  rw [p.hB_parameter, p.hB_parameter, p.hB_parameter, tor_mul, map_mul]

theorem nA_hA (t : Fˣ) :
    (p.signedRoots e).nA 1 * (p.signedRoots e).hA (Units.map e.extension.toMonoidHom t) *
      ((p.signedRoots e).nA 1)⁻¹ =
        (p.signedRoots e).hA (Units.map e.extension.toMonoidHom t⁻¹) := by
  rw [p.nA_one, p.hA_parameter, p.hA_parameter]
  change p.shortMap (weyl F) * p.shortMap (tor t) * (p.shortMap (weyl F))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, weyl_tor]

theorem nB_hB (t : Kˣ) :
    (p.signedRoots e).nB 1 * (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t) *
      ((p.signedRoots e).nB 1)⁻¹ =
        (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t⁻¹) := by
  rw [p.nB_one, p.hB_parameter, p.hB_parameter]
  change p.longMap (weyl K) * p.longMap (tor t) * (p.longMap (weyl K))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, weyl_tor]
end RankOnePair
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
