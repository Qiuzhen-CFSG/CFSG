module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.Inputs
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Character coverage for the SU₃(5) principal series

Characters of the actual Borel into a commutative group kill its root radical.
This follows directly from the Hermitian Heisenberg coordinates and the action
of the diagonal parameter `1/2`. Over a field of characteristic two, the
remaining torus values have cube one because the matrix field has 25 elements.
No field of definition for the coefficient character is assumed.

These character-coverage steps support a principal-series approach to the
degree assertion in Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, and Aschbacher–Smith K.2, printed p.453. The coordinates
and conjugation identity are those of Huppert II.10.12.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.OddPrimeSylow.NormalizedOuter
open HermitianForm.BorelTorus
namespace Representation.SU3.FiveSmallModules.Degrees

variable {F : Type*} [Field F] (J : HermitianForm 3 F)

private theorem root_pow_five [CharP F 5] (z : hermitianUnipotentCoord J) : z ^ 5 = 1 := by
  simp only [pow_succ, pow_zero, one_mul]
  apply Subtype.ext
  apply Prod.ext
  · change ((((z.val.1 + z.val.1) + z.val.1) + z.val.1) + z.val.1) = 0
    have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
    linear_combination z.val.1 * h5
  · change ((((z.val.2 + z.val.2 - z.val.1 * J.conj z.val.1) + z.val.2 -
      (z.val.1 + z.val.1) * J.conj z.val.1) + z.val.2 -
      (z.val.1 + z.val.1 + z.val.1) * J.conj z.val.1) + z.val.2 -
      (z.val.1 + z.val.1 + z.val.1 + z.val.1) * J.conj z.val.1) = 0
    have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
    linear_combination (z.val.2 - 2 * z.val.1 * J.conj z.val.1) * h5

/-- The literal root-coordinate homomorphism into the standard Borel. -/
def principalRootIn : hermitianUnipotentCoord (FormTransport.standardForm J) →*
    standardBorel J :=
  (hermitianUnipotentSU (FormTransport.standardForm J) rfl).codRestrict _
    (fun z => (show specialRoot _ _ ≤ standardBorel J from le_sup_left) ⟨z, rfl⟩)

/-- The literal full diagonal torus homomorphism into the standard Borel. -/
def principalTorusIn : Fˣ →* standardBorel J :=
  (hermitianTorusSU (FormTransport.standardForm J) rfl).codRestrict _
    (fun z => (show specialTorus _ _ ≤ standardBorel J from le_sup_right) ⟨z, rfl⟩)

variable {A : Type*} [CommGroup A]

private theorem character_root_action (χ : standardBorel J →* A) (k : Fˣ)
    (z : hermitianUnipotentCoord (FormTransport.standardForm J)) :
    χ (principalRootIn J (hermitianTorusAction (FormTransport.standardForm J) k z)) =
      χ (principalRootIn J z) := by
  have h : principalTorusIn J k * principalRootIn J z =
      principalRootIn J (hermitianTorusAction (FormTransport.standardForm J) k z) * principalTorusIn J k := by
    apply Subtype.ext
    apply Subtype.ext
    exact hermitianTorusGL_mul_unipotent _ _ _
  have hh := congrArg χ h
  simp only [map_mul] at hh
  exact mul_right_cancel (by simpa only [mul_comm] using hh.symm)

/-- Every character into a commutative group kills the unipotent radical.
The diagonal actor of parameter `1/2` scales root coordinates by 2 and 4;
its action first kills the central layer, then the first-coordinate quotient. -/
theorem borel_character_trivial_on_root [CharP F 5] (χ : standardBorel J →* A)
    (z : hermitianUnipotentCoord (FormTransport.standardForm J)) : χ (principalRootIn J z) = 1 := by
  have h2 : (2 : F) ≠ 0 := (CharP.cast_eq_zero_iff F 5 2).not.mpr (by decide)
  let k : Fˣ := (Units.mk0 2 h2)⁻¹
  have hfirst (w : hermitianUnipotentCoord (FormTransport.standardForm J)) :
      (hermitianTorusAction (FormTransport.standardForm J) k w).val.1 = 2 * w.val.1 := by
    simp only [hermitianTorusAction_fst, k, Units.val_inv_eq_inv_val, Units.val_mk0,
      FormTransport.standardForm_conj, map_inv₀, map_ofNat, inv_inv]
    field_simp
  have hsecond (w : hermitianUnipotentCoord (FormTransport.standardForm J)) :
      (hermitianTorusAction (FormTransport.standardForm J) k w).val.2 = 4 * w.val.2 := by
    simp only [hermitianTorusAction_snd, k, Units.val_inv_eq_inv_val, Units.val_mk0,
      FormTransport.standardForm_conj, map_inv₀, map_ofNat, inv_inv]
    ring
  have hc (w : hermitianUnipotentCoord (FormTransport.standardForm J)) (hw : w.val.1 = 0) :
      χ (principalRootIn J w) = 1 := by
    have he : hermitianTorusAction (FormTransport.standardForm J) k w = w ^ 4 := by
      simp only [pow_succ, pow_zero, one_mul]
      apply Subtype.ext
      apply Prod.ext
      · rw [hfirst, hw]
        change 2 * 0 = ((w.val.1 + w.val.1) + w.val.1) + w.val.1
        simp [hw]
      · rw [hsecond]
        change 4 * w.val.2 =
          ((w.val.2 + w.val.2 - w.val.1 * J.conj w.val.1) + w.val.2 -
            (w.val.1 + w.val.1) * J.conj w.val.1) + w.val.2 -
            (w.val.1 + w.val.1 + w.val.1) * J.conj w.val.1
        rw [hw]
        ring
    have he4 := character_root_action J χ k w
    rw [he, map_pow, map_pow] at he4
    have he5 : χ (principalRootIn J w) ^ 5 = 1 := by
      rw [← map_pow, ← map_pow, root_pow_five, map_one, map_one]
    have he2 : χ (principalRootIn J w) ^ 2 = 1 := by
      simpa only [pow_succ, he4, ← pow_two] using he5
    have he4' : χ (principalRootIn J w) ^ 4 = 1 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, he2, one_pow]
    exact he4.symm.trans he4'
  let w := hermitianTorusAction (FormTransport.standardForm J) k z * (z ^ 2)⁻¹
  have hw : w.val.1 = 0 := by
    dsimp only [w]
    rw [pow_two]
    change (hermitianTorusAction (FormTransport.standardForm J) k z).val.1 +
      -(z.val.1 + z.val.1) = 0
    rw [hfirst]
    ring
  have hh := hc w hw
  change χ (principalRootIn J (hermitianTorusAction (FormTransport.standardForm J) k z * (z ^ 2)⁻¹)) = 1 at hh
  simp only [map_mul, map_inv, map_pow, character_root_action] at hh
  have he : χ (principalRootIn J z) = χ (principalRootIn J z) ^ 2 := mul_inv_eq_one.mp hh
  exact mul_left_cancel (a := χ (principalRootIn J z)) (by simpa only [mul_one, pow_two] using he.symm)

/-- Every Borel character over a characteristic-two field has cubic values.
The root group is killed and the torus has order 24. The eighth-power
Frobenius is injective, leaving only the cubic part of that order. -/
theorem borel_character_cube [Finite F] (hc : Nat.card F = 5 ^ 2)
    {K : Type*} [Field K] [CharP K 2] (χ : standardBorel J →* Kˣ)
    (b : standardBorel J) : χ b ^ 3 = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : CharP F 5 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
  let N : Subgroup (standardBorel J) := ((powMonoidHom 3).comp χ).ker
  have hr : specialRoot (FormTransport.standardForm J) rfl ≤
      N.map (standardBorel J).subtype := by
    rintro _ ⟨z, rfl⟩
    refine ⟨principalRootIn J z, ?_, rfl⟩
    change χ (principalRootIn J z) ^ 3 = 1
    rw [borel_character_trivial_on_root J χ z, one_pow]
  have ht : specialTorus (FormTransport.standardForm J) rfl ≤
      N.map (standardBorel J).subtype := by
    rintro _ ⟨k, rfl⟩
    refine ⟨principalTorusIn J k, ?_, rfl⟩
    change χ (principalTorusIn J k) ^ 3 = 1
    have hk : k ^ 24 = 1 := by
      have hh := pow_card_eq_one (x := k)
      have hcard : Fintype.card Fˣ = 24 := by
        rw [← Nat.card_eq_fintype_card, Nat.card_units, hc]
        norm_num
      rwa [hcard] at hh
    have hh : χ (principalTorusIn J k) ^ 24 = 1 := by
      rw [← map_pow, ← map_pow, hk, map_one, map_one]
    apply Units.ext
    have hp : (χ (principalTorusIn J k) : K) ^ (2 ^ 3 * 3) = 1 :=
      congrArg (fun x : Kˣ => (x : K)) hh
    exact (ExpChar.pow_prime_pow_mul_eq_one_iff 2 3 3 _).mp hp
  have hB : standardBorel J ≤ N.map (standardBorel J).subtype := sup_le hr ht
  obtain ⟨c, hcN, he⟩ := hB b.property
  have he' : c = b := Subtype.ext he
  subst c
  exact hcN

end Representation.SU3.FiveSmallModules.Degrees
