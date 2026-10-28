module

public import Theory.SpecificGroups.Triality.LeviFields

/-!
# The cubic trace pairing for the triality arms radical

The root pairs (4,8), (5,9), and (6,7) in the published orbit ordering
produce Tr(a F(b)). The three-term Frobenius trace lands in the actual
fixed field. In characteristic two its restriction to that field is the
identity, so inversion and F² give explicit surjectivity witnesses for each
nonzero argument. These proofs include q = 2.

Source: GLS3 2.4.5(b), especially the trace commutator relation
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith F.1.11–12
(`refs/quasithin.pdf`, printed pp.262–264).
-/

@[expose] public section

noncomputable section
namespace Triality.Standard.RadicalCoordinates.Centers

/-- The three-term Frobenius trace, with its actual fixed-field codomain. -/
def cubicTrace (P : Parameters) : ExtensionField P →+ fixedField P where
  toFun x := ⟨x + fieldFrobenius P x + fieldFrobenius P (fieldFrobenius P x), by
    change fieldFrobenius P _ = _
    simp only [map_add, fieldFrobenius_three]
    abel⟩
  map_zero' := by apply Subtype.ext; simp [-fieldFrobenius_apply]
  map_add' x y := by apply Subtype.ext; simp only [map_add, Subfield.coe_add]; abel

@[simp] theorem cubicTrace_coe (P : Parameters) (x : ExtensionField P) :
    (cubicTrace P x : ExtensionField P) =
      x + fieldFrobenius P x + fieldFrobenius P (fieldFrobenius P x) := rfl

/-- In characteristic two the degree-three trace restricts to the identity. -/
theorem cubicTrace_fixed (P : Parameters) (hp : P.prime = 2) (x : fixedField P) :
    cubicTrace P x.val = x := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  apply Subtype.ext
  have hx : fieldFrobenius P x.val = x.val := x.property
  simp only [cubicTrace_coe, hx, CharTwo.add_self_eq_zero, zero_add]

theorem cubicTrace_surjective (P : Parameters) (hp : P.prime = 2) :
    Function.Surjective (cubicTrace P) :=
  fun x => ⟨x.val, cubicTrace_fixed P hp x⟩

/-- Pairing for root orbits (4,5,6) and (7,8,9) in the published ordering.
The root-sum pairs are (4,8), (5,9), and (6,7). -/
def armsPairing (P : Parameters) (a b : ExtensionField P) : fixedField P :=
  cubicTrace P (a * fieldFrobenius P b)

theorem armsPairing_coe (P : Parameters) (a b : ExtensionField P) :
    (armsPairing P a b : ExtensionField P) =
      a * fieldFrobenius P b + fieldFrobenius P a * fieldFrobenius P (fieldFrobenius P b) +
        fieldFrobenius P (fieldFrobenius P a) * b := by
  simp only [armsPairing, cubicTrace_coe, map_mul, fieldFrobenius_three]

@[simp] theorem armsPairing_zero_left (P : Parameters) (b : ExtensionField P) :
    armsPairing P 0 b = 0 := by simp [armsPairing]

@[simp] theorem armsPairing_zero_right (P : Parameters) (a : ExtensionField P) :
    armsPairing P a 0 = 0 := by simp [armsPairing, -fieldFrobenius_apply]

theorem armsPairing_add_left (P : Parameters) (a b c : ExtensionField P) :
    armsPairing P (a + b) c = armsPairing P a c + armsPairing P b c := by
  simp [armsPairing, add_mul]

theorem armsPairing_add_right (P : Parameters) (a b c : ExtensionField P) :
    armsPairing P a (b + c) = armsPairing P a b + armsPairing P a c := by
  simp [armsPairing, mul_add, -fieldFrobenius_apply]

/-- Every nonzero first argument induces a surjection onto the fixed field.
The witness uses F², which is the inverse of F, and works also when q = 2. -/
theorem armsPairing_surjective_right (P : Parameters) (hp : P.prime = 2)
    (a : ExtensionField P) (ha : a ≠ 0) : Function.Surjective (armsPairing P a) := by
  intro z
  refine ⟨fieldFrobenius P (fieldFrobenius P (a⁻¹ * z.val)), ?_⟩
  simp only [armsPairing, fieldFrobenius_three, ← mul_assoc, mul_inv_cancel₀ ha,
    one_mul, cubicTrace_fixed P hp]

theorem armsPairing_surjective_left (P : Parameters) (hp : P.prime = 2)
    (b : ExtensionField P) (hb : b ≠ 0) :
    Function.Surjective (fun a => armsPairing P a b) := by
  intro z
  have hf : fieldFrobenius P b ≠ 0 := (map_ne_zero (fieldFrobenius P)).mpr hb
  refine ⟨z.val * (fieldFrobenius P b)⁻¹, ?_⟩
  simp only [armsPairing, mul_assoc, inv_mul_cancel₀ hf, mul_one, cubicTrace_fixed P hp]

theorem armsPairing_left_nondegenerate (P : Parameters) (hp : P.prime = 2)
    (a : ExtensionField P) (h : ∀ b, armsPairing P a b = 0) : a = 0 := by
  by_contra ha
  obtain ⟨b, hb⟩ := armsPairing_surjective_right P hp a ha 1
  exact one_ne_zero (hb.symm.trans (h b))

theorem armsPairing_right_nondegenerate (P : Parameters) (hp : P.prime = 2)
    (b : ExtensionField P) (h : ∀ a, armsPairing P a b = 0) : b = 0 := by
  by_contra hb
  obtain ⟨a, ha⟩ := armsPairing_surjective_left P hp b hb 1
  exact one_ne_zero (ha.symm.trans (h a))

end Triality.Standard.RadicalCoordinates.Centers
