module

public import Theory.SpecificGroups.PSL3Four.SylowModel.QuaternionCoordinates
public import Theory.GroupTheory.QuaternionGenerated
/-!
# Explicit quaternion factors of the exceptional trace kernel

Write a,b for the two prime-field root elements, c for the highest-root element
with coordinate ω, and d for Frobenius. The actual subgroups
B = ⟨ab, acd⟩ and D = ⟨cd, abc⟩ are quaternion groups of order eight.

Coordinate calculation gives a common nontrivial square, inversion within each
pair, and commutation across the pairs. The quaternion presentation API gives
actual multiplicative equivalences. The four original root and field elements
are recovered from these generators, so B and D generate Q. Their intersection
is exactly the already computed center of Q, of order two.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §5.3.7,
printed pp. 660–661 (PDF pp. 677–678). The common-square recognition argument
also appears in `Theory.GroupTheory.HyperbolicQuaternionFactors`.
-/

@[expose] public section
namespace Matrix.PSL3Four.SylowModel
noncomputable section

/-- Highest-root elements, restricted to the trace kernel. -/
def coreCentral : Multiplicative F →* Q where
  toFun c := ⟨inclusion (central c), Z_le_Q ⟨c,rfl⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' c d := Subtype.ext (by simp)

def rootC : Q := coreCentral (Multiplicative.ofAdd omega)
def coreZ : Q := coreCentral (Multiplicative.ofAdd 1)

theorem coreZ_ne_one : coreZ ≠ 1 := fun h => z_ne_one (congrArg Subtype.val h)
theorem coreZ_sq : coreZ ^ 2 = 1 := Subtype.ext z_sq

@[simp] theorem tau_sq : τ * τ = 1 := by decide

/-- The two quaternion generators in the first factor. -/
def qi : Q := rootA * rootB
def qj : Q := rootA * (rootC * fieldD)
/-- The two quaternion generators in the second factor. -/
def qk : Q := rootC * fieldD
def ql : Q := (rootA * rootB) * rootC

theorem quaternion_squares :
    qi ^ 2 = coreZ ∧ qj ^ 2 = coreZ ∧ qk ^ 2 = coreZ ∧ ql ^ 2 = coreZ := by
  have hw := omega_frobenius
  have hh : omega + (omega + 1) = 1 := by
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    apply Subtype.ext <;> apply SemidirectProduct.ext
  all_goals first
    | apply U.ext <;> simp [qi, qj, qk, ql, rootA, rootB, rootC, coreZ, fieldD,
        coreCentral, inclusion, central, pow_two, hw, hh, CharTwo.add_self_eq_zero]
    | simp [qi, qj, qk, ql, rootA, rootB, rootC, coreZ, fieldD,
        coreCentral, inclusion, central, pow_two]

private theorem core_inverse (a : Q) (ha : a ^ 2 = coreZ) : a⁻¹ = coreZ * a := by
  apply inv_eq_of_mul_eq_one_left
  rw [mul_assoc, ← pow_two, ha, ← pow_two, coreZ_sq]

theorem quaternion_inversion :
    qj * qi * qj⁻¹ = qi⁻¹ ∧ ql * qk * ql⁻¹ = qk⁻¹ := by
  constructor
  · apply mul_inv_eq_iff_eq_mul.mpr
    rw [core_inverse qi quaternion_squares.1]
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply U.ext <;> simp [qi, qj, rootA, rootB, rootC, coreZ, fieldD,
        coreCentral, inclusion, central, CharTwo.add_self_eq_zero]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp [qi, qj, rootA, rootB, rootC, coreZ, fieldD,
        coreCentral, inclusion, central]
  · apply mul_inv_eq_iff_eq_mul.mpr
    rw [core_inverse qk quaternion_squares.2.2.1]
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply U.ext <;> simp [qk, ql, rootA, rootB, rootC, coreZ, fieldD,
        coreCentral, inclusion, central, CharTwo.add_self_eq_zero]
      rw [← fieldFrobenius_apply, omega_frobenius, ← add_assoc,
        add_comm (1 : F) omega, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp [qk, ql, rootA, rootB, rootC, coreZ, fieldD,
        coreCentral, inclusion, central]

/-- The four root and field involutions generate the whole trace kernel. -/
theorem core_generators_generate (H : Subgroup Q)
    (ha : rootA ∈ H) (hb : rootB ∈ H) (hc : rootC ∈ H) (hd : fieldD ∈ H) : H = ⊤ := by
  have hz : coreZ ∈ H := quaternion_squares.1 ▸ H.pow_mem (H.mul_mem ha hb) 2
  have hcentral (c : F) : coreCentral (Multiplicative.ofAdd c) ∈ H := by
    rcases field_cases c with rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact hz
    · exact hc
    · change coreCentral (Multiplicative.ofAdd omega * Multiplicative.ofAdd 1) ∈ H
      rw [map_mul]
      exact H.mul_mem hc hz
  apply top_unique
  intro g _
  have hx := ((mem_Q _).mp g.property).1
  have hy := ((mem_Q _).mp g.property).2
  let X : Q := ⟨⟨⟨g.val.left.x, 0, 0⟩, 1⟩, (mem_Q _).mpr ⟨hx, by simp⟩⟩
  let Y : Q := ⟨⟨⟨0, g.val.left.y, 0⟩, 1⟩, (mem_Q _).mpr ⟨by simp, hy⟩⟩
  let R : Q := ⟨SemidirectProduct.inr g.val.right, (mem_Q _).mpr ⟨by simp, by simp⟩⟩
  have hX : X ∈ H := by
    rcases (frobenius_fixed_iff _).mp hx with hx | hx
    · have he : X = 1 := Subtype.ext (SemidirectProduct.ext (U.ext hx rfl rfl) rfl)
      rw [he]; exact H.one_mem
    · have he : X = rootA := Subtype.ext (SemidirectProduct.ext (U.ext hx rfl rfl) rfl)
      rw [he]; exact ha
  have hY : Y ∈ H := by
    rcases (frobenius_fixed_iff _).mp hy with hy | hy
    · have he : Y = 1 := Subtype.ext (SemidirectProduct.ext (U.ext rfl hy rfl) rfl)
      rw [he]; exact H.one_mem
    · have he : Y = rootB := Subtype.ext (SemidirectProduct.ext (U.ext rfl hy rfl) rfl)
      rw [he]; exact hb
  have hR : R ∈ H := by
    rcases c2_cases g.val.right with hr | hr
    · have he : R = 1 := Subtype.ext (SemidirectProduct.ext rfl hr)
      rw [he]; exact H.one_mem
    · have he : R = fieldD := Subtype.ext (SemidirectProduct.ext rfl hr)
      rw [he]; exact hd
  have he : g = X * Y * coreCentral (Multiplicative.ofAdd
      (g.val.left.c + g.val.left.x * g.val.left.y)) * R := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply U.ext <;> simp [X, Y, R, coreCentral, inclusion, central,
        add_left_comm, CharTwo.add_self_eq_zero]
    · simp [X, Y, R, coreCentral, inclusion]
  rw [he]
  exact H.mul_mem (H.mul_mem (H.mul_mem hX hY) (hcentral _)) hR

/-- The first explicit quaternion factor, generated by ab and acd. -/
def B : Subgroup Q := Subgroup.closure ({qi, qj} : Set Q)
/-- The second explicit quaternion factor, generated by cd and abc. -/
def D : Subgroup Q := Subgroup.closure ({qk, ql} : Set Q)

private theorem quaternion_model (a b : Q) (ha : a ^ 2 = coreZ)
    (hb : b ^ 2 = coreZ) (hinv : b * a * b⁻¹ = a⁻¹) :
    Nonempty (Subgroup.closure ({a,b} : Set Q) ≃* QuaternionGroup 2) := by
  have ha4 : orderOf a = 4 := by
    have hn : a ^ 2 ≠ 1 := by rw [ha]; exact coreZ_ne_one
    have h4 : a ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, ha, coreZ_sq]
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hn) (by simpa using h4)
  refine (QuaternionGroup.closure_equiv_of_relations (m := 2) (by decide)
    a b ha4 (hb.trans ha.symm) hinv ?_).2
  rintro ⟨i, rfl⟩
  have hcomm : a ^ i * a * (a ^ i)⁻¹ = a := by group
  have hai : a = a⁻¹ := hcomm.symm.trans hinv
  apply coreZ_ne_one
  rw [← ha, pow_two]
  exact (congrArg (· * a) hai).trans (inv_mul_cancel a)

def quaternionBEquiv : B ≃* QuaternionGroup 2 := Classical.choice
  (by exact quaternion_model qi qj quaternion_squares.1 quaternion_squares.2.1 quaternion_inversion.1)

def quaternionDEquiv : D ≃* QuaternionGroup 2 := Classical.choice
  (by exact quaternion_model qk ql quaternion_squares.2.2.1 quaternion_squares.2.2.2 quaternion_inversion.2)

theorem quaternion_cross_commute :
    Commute qi qk ∧ Commute qi ql ∧ Commute qj qk ∧ Commute qj ql := by
  have hw : omega ^ 2 = omega + 1 := omega_frobenius
  refine ⟨?_, ?_, ?_, ?_⟩ <;> change _ = _
  all_goals
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply U.ext <;> simp [qi, qj, qk, ql, rootA, rootB, rootC, fieldD,
        coreCentral, inclusion, central, hw, add_comm, add_left_comm, CharTwo.add_self_eq_zero] <;>
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    · simp [qi, qj, qk, ql, rootA, rootB, rootC, fieldD,
        coreCentral, inclusion, central]

theorem B_sup_D : B ⊔ D = ⊤ := by
  have hi : qi ∈ B ⊔ D := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hj : qj ∈ B ⊔ D := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hk : qk ∈ B ⊔ D := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hl : ql ∈ B ⊔ D := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have ha : rootA ∈ B ⊔ D := by
    have h := (B ⊔ D).mul_mem hj ((B ⊔ D).inv_mem hk)
    simpa [qj, qk, mul_assoc] using h
  have hc : rootC ∈ B ⊔ D := by
    have h := (B ⊔ D).mul_mem ((B ⊔ D).inv_mem hi) hl
    simpa [qi, ql, mul_assoc] using h
  apply core_generators_generate (B ⊔ D) ha ?_ hc ?_
  · have h := (B ⊔ D).mul_mem ((B ⊔ D).inv_mem ha) hi
    simpa [qi, mul_assoc] using h
  · have h := (B ⊔ D).mul_mem ((B ⊔ D).inv_mem hc) hk
    simpa [qk, mul_assoc] using h

theorem B_D_commute : ∀ b ∈ B, ∀ d ∈ D, b * d = d * b := by
  have hle : B ≤ Subgroup.centralizer (D : Set Q) := by
    rw [D, Subgroup.centralizer_closure]
    apply (Subgroup.closure_le _).mpr
    intro b hb
    rcases (show b = qi ∨ b = qj by simpa using hb) with rfl | rfl
    · intro d hd
      rcases (show d = qk ∨ d = ql by simpa using hd) with rfl | rfl
      · exact quaternion_cross_commute.1.symm.eq
      · exact quaternion_cross_commute.2.1.symm.eq
    · intro d hd
      rcases (show d = qk ∨ d = ql by simpa using hd) with rfl | rfl
      · exact quaternion_cross_commute.2.2.1.symm.eq
      · exact quaternion_cross_commute.2.2.2.symm.eq
  exact fun b hb d hd => (hle hb d hd).symm

theorem B_inf_D : B ⊓ D = Subgroup.center Q := by
  apply le_antisymm
  · intro x hx
    apply Subgroup.mem_center_iff.mpr
    have hB : B ≤ Subgroup.centralizer ({x} : Set Q) := by
      intro b hb y hy
      have hy' : y = x := hy
      subst y
      exact (B_D_commute b hb x hx.2).symm
    have hD : D ≤ Subgroup.centralizer ({x} : Set Q) := by
      intro d hd y hy
      have hy' : y = x := hy
      subst y
      exact B_D_commute x hx.1 d hd
    have ht := sup_le hB hD
    rw [B_sup_D] at ht
    intro g
    exact (ht (Subgroup.mem_top g) x (by simp)).symm
  · intro x hx
    have hzB : coreZ ∈ B := quaternion_squares.1 ▸
      B.pow_mem (Subgroup.subset_closure (by simp)) 2
    have hzD : coreZ ∈ D := quaternion_squares.2.2.1 ▸
      D.pow_mem (Subgroup.subset_closure (by simp)) 2
    rw [center_Q_eq] at hx
    have hx' := (mem_C_iff x.val).mp hx
    rcases hx' with h | h
    · have he : x = 1 := Subtype.ext h
      rw [he]
      exact (B ⊓ D).one_mem
    · have he : x = coreZ := Subtype.ext h
      rw [he]
      exact ⟨hzB, hzD⟩

theorem card_B_inf_D : Nat.card (B ⊓ D : Subgroup Q) = 2 := by
  rw [B_inf_D, card_center_Q]

theorem card_B : Nat.card B = 8 := by
  rw [Nat.card_congr quaternionBEquiv.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem card_D : Nat.card D = 8 := by
  rw [Nat.card_congr quaternionDEquiv.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

end
end Matrix.PSL3Four.SylowModel
