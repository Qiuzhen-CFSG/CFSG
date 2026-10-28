module

public import ABG.ChapterII.Section1.WreathedInvolutions
public import ABG.ChapterII.Section1.WreathedDiagonalOrder
public import Theory.Character.VanishingCentralizer

/-!
# Fong's generators and the character input for the Borel construction

Fong's generators are expressed in the chosen ABG wreathed presentation.
In particular his element `F` is `s*z`, whereas his later element `R` of
order three is unrelated to the ABG generator `r`. The power identities
below transfer the presentation into the ambient group without fusion
assumptions.

`CharacterData` records only the genuine irreducible characters and values
used in the last paragraph of Fong's argument. It contains no subgroup or
action existence assumption. Its witnesses must be supplied by the preceding
character calculation.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), 65–76, presentation on p.68,
equation (10) on p.73, and the Borel construction on p.75.
-/

namespace Stellmacher.Recognition.FongWreathed

variable {G : Type*} [Group G] {S : Sylow 2 G}
variable (P : ABG.Wreathed.Presentation S 2)

@[expose] public def F : G := ((P.s * P.z : S) : G)
@[expose] public def E : G := (P.s : G)
@[expose] public def X : G := ((P.s ^ 2 : S) : G)
@[expose] public def J : G := F P ^ 4

public theorem F_sq : F P ^ 2 = (P.u : G) := by
  exact congrArg Subtype.val P.sz_sq

public theorem E_sq : E P ^ 2 = X P := rfl

public theorem X_sq : X P ^ 2 = 1 := by
  change (((P.s ^ 2) ^ 2 : S) : G) = 1
  rw [← pow_mul]
  exact congrArg Subtype.val P.s_pow

public theorem J_eq_x : J P = (P.x : G) := by
  change F P ^ 4 = _
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, F_sq]
  rfl

public theorem J_eq_r_sq : J P = ((P.r ^ 2 : S) : G) := by
  rw [J_eq_x]
  exact congrArg Subtype.val (by simpa using P.r_half.symm)

public theorem orderOf_J : orderOf (J P) = 2 := by
  rw [J_eq_x, Subgroup.orderOf_coe, P.x_orderOf]

public theorem orderOf_X : orderOf (X P) = 2 := by
  change orderOf (P.x₂ : G) = 2
  rw [Subgroup.orderOf_coe, P.x₂_orderOf]

public theorem orderOf_F_sq : orderOf (F P ^ 2) = 4 := by
  rw [F_sq, Subgroup.orderOf_coe, P.orderOf_u]
  norm_num

public theorem orderOf_F : orderOf (F P) = 8 := by
  have hJ := orderOf_J P
  have hfour : F P ^ 4 ≠ 1 := by
    intro h
    change orderOf (F P ^ 4) = 2 at hJ
    rw [h, orderOf_one] at hJ
    omega
  have height : F P ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul]
    change J P ^ 2 = 1
    rw [← hJ, pow_orderOf_eq_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 2) hfour height

public theorem X_mul_F_sq : X P * F P ^ 2 = (P.r⁻¹ : S) := by
  rw [F_sq]
  change (((P.s ^ 2 * P.u : S)) : G) = _
  apply congrArg Subtype.val
  have hs4 : P.s ^ 4 = 1 := P.s_pow
  have hs3 : P.s ^ 3 = P.s⁻¹ := by
    apply mul_left_cancel (a := P.s)
    rw [← pow_succ', hs4, mul_inv_cancel]
  change P.s ^ 2 * (P.s * P.t) = (P.s * P.t⁻¹)⁻¹
  rw [← mul_assoc, ← pow_succ, hs3, mul_inv_rev, inv_inv]
  exact (show Commute P.s P.t from P.commute).inv_left.eq

public theorem E_inv_mul_F_mul_E : (E P)⁻¹ * F P * E P = X P * F P ^ 3 := by
  change (((P.s⁻¹ * (P.s * P.z) * P.s : S)) : G) = _
  have heq : P.s⁻¹ * (P.s * P.z) * P.s = P.s ^ 2 * (P.s * P.z) ^ 3 := by
    have hs4 : P.s ^ 4 = 1 := P.s_pow
    calc
      P.s⁻¹ * (P.s * P.z) * P.s = P.t * P.z := by
        rw [inv_mul_cancel_left, P.z_mul_s]
      _ = P.s ^ 4 * (P.t * P.z) := by rw [hs4, one_mul]
      _ = P.s ^ 2 * ((P.s * P.t) * (P.s * P.z)) := by
        symm
        calc
          P.s ^ 2 * ((P.s * P.t) * (P.s * P.z)) = P.s ^ 3 * (P.t * P.s) * P.z := by group
          _ = P.s ^ 3 * (P.s * P.t) * P.z := by rw [← P.commute]
          _ = P.s ^ 4 * (P.t * P.z) := by group
      _ = P.s ^ 2 * (P.s * P.z) ^ 3 := by
        rw [show (P.s * P.z) ^ 3 = (P.s * P.z) ^ 2 * (P.s * P.z) from pow_succ _ 2,
          P.sz_sq]
        rfl
  exact congrArg Subtype.val heq

/-- The eight entries of Fong's `F` column, in the supplied character order. -/
@[expose] public def fColumn : Fin 8 → ℂ :=
  ![1, 1, -1, -1, Complex.I, -Complex.I, Complex.I, -Complex.I]

/-- Explicit character hypotheses for the implication on Fong p.75. -/
public structure CharacterData where
  chi : Fin 8 → ClassFunction G
  irreducible : ∀ i, IsIrreducibleCharacter (chi i)
  injective : Function.Injective chi
  principal : chi 0 = 1
  degree : chi 1 1 = 27
  integer_values : ∀ g, ∃ z : ℤ, chi 1 g = z
  at_J : chi 1 (J P) = 3
  at_X_mul_F_sq : chi 1 (X P * F P ^ 2) = -1
  at_F_sq : chi 1 (F P ^ 2) = 3
  vanishes : ∀ g, 3 ∣ orderOf g → chi 1 g = 0
  at_F : ∀ i, chi i (F P) = fColumn i

namespace CharacterData

variable {P} (c : CharacterData P)

public theorem distinguished_isCharacter : IsCharacter (c.chi 1) := by
  obtain ⟨n, ρ, _, hρ⟩ := c.irreducible 1
  exact ⟨n, ρ, hρ⟩

include c in
/-- The character congruence excludes the odd-core obstruction on Fong p.75. -/
public theorem three_not_dvd_centralizer_X_mul_F_sq [Finite G] :
    ¬ 3 ∣ Nat.card (Subgroup.centralizer ({X P * F P ^ 2} : Set G)) := by
  exact IsCharacter.prime_not_dvd_centralizer_card_of_vanishing c.distinguished_isCharacter
    Nat.prime_three c.vanishes _ (-1) (by simpa using c.at_X_mul_F_sq) (by norm_num)

include c in
public theorem three_not_dvd_centralizer_F [Finite G] :
    ¬ 3 ∣ Nat.card (Subgroup.centralizer ({F P} : Set G)) := by
  exact IsCharacter.prime_not_dvd_centralizer_card_of_vanishing c.distinguished_isCharacter
    Nat.prime_three c.vanishes _ 1 (by simpa [fColumn] using c.at_F 1) (by norm_num)

public theorem vanishes_on_subgroup27 (Q : Subgroup G) (hQ : Nat.card Q = 27)
    (q : Q) (hq : q ≠ 1) : c.chi 1 (q : G) = 0 := by
  have hP : IsPGroup 3 Q := IsPGroup.of_card (show Nat.card Q = 3 ^ 3 from hQ)
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply c.vanishes
  rw [Subgroup.orderOf_coe]
  exact hP.dvd_orderOf hq

end CharacterData

/-- The subgroup witnesses to be constructed from the local and character
data. This is an output specification, not an additional character input. -/
public structure BorelSubgroups where
  R : G
  Q : Subgroup G
  B : Subgroup G
  order_R : orderOf R = 3
  card_Q : Nat.card Q = 27
  R_mem_center : R ∈ (Subgroup.center Q).map Q.subtype
  F_inverts_R : (F P)⁻¹ * R * F P = R⁻¹
  centralizer_R : Subgroup.centralizer ({R} : Set G) = Subgroup.zpowers (F P ^ 2) ⊔ Q
  normalizer_R : Subgroup.normalizer (Subgroup.zpowers R : Set G) = B
  B_eq : B = Subgroup.zpowers (F P) ⊔ Q
  Q_normalized : B ≤ Subgroup.normalizer (Q : Set G)

end Stellmacher.Recognition.FongWreathed
