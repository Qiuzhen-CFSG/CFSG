module

public import Theory.GroupAction.C4SquareAutomorphismOrder
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

/-!
# Maximal two-subgroups of the automorphism group of C₄ × C₄

An automorphism stabilizing a nonzero involution is determined by one of 32
ordered bases. A two-group acting on the three nonzero involutions fixes one;
therefore every automorphism subgroup of order 32 is its full stabilizer.
This stabilizer contains a central transvection which fixes all involutions
and inverts only elements of square one.

The basis counts and the transvection identities are finite coordinate
calculations checked with `decide`. This supplies the automorphism side of
the maximal extension problem in Janko–Thompson, Math. Z. 113 (1970), 1.4,
printed p.386. It does not assert that an involution action has an involution
lift in an extension.
-/

namespace C4SquareExtension
private def first : Model := (Multiplicative.ofAdd 1, 1)
private def second : Model := (1, Multiplicative.ofAdd 1)
private def eval (a b x : Model) : Model := a ^ x.1.toAdd.val * b ^ x.2.toAdd.val
private theorem eval_std : ∀ x : Model, eval first second x = x := by decide
private theorem hom_eval (f : MulAut Model) (x : Model) :
    f x = eval (f first) (f second) x := by
  conv_lhs => rw [← eval_std x]
  simp only [eval, map_mul, map_pow]
private theorem hom_ext (f g : MulAut Model) (ha : f first = g first)
    (hb : f second = g second) : f = g := by
  apply MulEquiv.ext
  intro x
  rw [hom_eval f, hom_eval g, ha, hb]
private def Good (p : Model × Model) : Prop :=
  p.1 ^ 2 ≠ 1 ∧ p.2 ^ 2 ≠ 1 ∧ p.1 ^ 2 ≠ p.2 ^ 2
private instance (p : Model × Model) : Decidable (Good p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem good_fixed_card : ∀ z : Model, z ^ 2 = 1 → z ≠ 1 →
    Nat.card {p : Model × Model // Good p ∧ eval p.1 p.2 z = z} = 32 := by
  intro z
  rw [Nat.card_eq_fintype_card]
  revert z
  decide
private theorem good_aut (f : MulAut Model) : Good (f first, f second) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : first ^ 2 = 1 := f.injective (by simpa only [map_pow, map_one] using h)
    exact (by decide : first ^ 2 ≠ 1) this
  · intro h
    have : second ^ 2 = 1 := f.injective (by simpa only [map_pow, map_one] using h)
    exact (by decide : second ^ 2 ≠ 1) this
  · intro h
    have : first ^ 2 = second ^ 2 := f.injective (by simpa only [map_pow] using h)
    exact (by decide : first ^ 2 ≠ second ^ 2) this

public theorem model_stabilizer_card_le (z : Model) (hz : z ^ 2 = 1) (hne : z ≠ 1) :
    Nat.card (MulAction.stabilizer (MulAut Model) z) ≤ 32 := by
  let X := {p : Model × Model // Good p ∧ eval p.1 p.2 z = z}
  let f : MulAction.stabilizer (MulAut Model) z → X := fun a =>
    ⟨(a.val first, a.val second), good_aut a.val, (hom_eval a.val z).symm.trans a.property⟩
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply hom_ext
    · exact congrArg (fun p : X => p.val.1) h
    · exact congrArg (fun p : X => p.val.2) h
  exact (Nat.card_le_card_of_injective f hinj).trans (le_of_eq (good_fixed_card z hz hne))

public theorem model_eq_stabilizer_of_card_eq_thirty_two (C : Subgroup (MulAut Model))
    (hC : IsPGroup 2 C) (hc : Nat.card C = 32) :
    ∃ z : Model, z ^ 2 = 1 ∧ z ≠ 1 ∧ C = MulAction.stabilizer (MulAut Model) z := by
  let X : SubMulAction C Model := {
    carrier := {x | x ^ 2 = 1 ∧ x ≠ 1}
    smul_mem' := by
      intro a x hx
      constructor
      · change ((a : MulAut Model) x) ^ 2 = 1
        rw [← map_pow, hx.1, map_one]
      · intro h
        exact hx.2 ((a : MulAut Model).injective (h.trans (map_one a.val).symm)) }
  have hcard : Nat.card X = 3 := by
    change Nat.card {x : Model // x ^ 2 = 1 ∧ x ≠ 1} = 3
    rw [Nat.card_eq_fintype_card]
    decide
  have hp : ¬ 2 ∣ Nat.card X := by rw [hcard]; decide
  obtain ⟨z, hz⟩ := hC.nonempty_fixed_point_of_prime_not_dvd_card X hp
  refine ⟨z.val, z.property.1, z.property.2, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge
  · intro a ha
    change a z.val = z.val
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hz ⟨a, ha⟩)
  · rw [hc]
    exact model_stabilizer_card_le z.val z.property.1 z.property.2

private def transvection (z x : Model) : Model :=
  if z = first ^ 2 then (x.1 * x.2 ^ 2, x.2)
  else if z = second ^ 2 then (x.1, x.2 * x.1 ^ 2)
  else (x.1⁻¹ * x.2 ^ 2, x.1 ^ 2 * x.2⁻¹)
private theorem transvection_invol : ∀ z x : Model,
    transvection z (transvection z x) = x := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem transvection_mul : ∀ z x y : Model,
    transvection z (x * y) = transvection z x * transvection z y := by decide
private def centralAut (z : Model) : MulAut Model where
  toFun := transvection z
  invFun := transvection z
  left_inv := transvection_invol z
  right_inv := transvection_invol z
  map_mul' := transvection_mul z
private theorem centralAut_fixes_binary : ∀ z x : Model,
    x ^ 2 = 1 → transvection z x = x := by decide
private theorem centralAut_inverts_only_binary : ∀ z x : Model,
    transvection z x = x⁻¹ → x ^ 2 = 1 := by decide
private theorem centralAut_nonidentity : ∀ z : Model,
    transvection z first ≠ first ∨ transvection z second ≠ second := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem centralAut_commutes : ∀ z a b : Model,
    z ^ 2 = 1 → z ≠ 1 → Good (a,b) → eval a b z = z →
    transvection z a = eval a b (transvection z first) ∧
      transvection z b = eval a b (transvection z second) := by
  unfold Good
  decide

/-- A maximal two-subgroup of the automorphism group contains a nontrivial
central involution which fixes the binary elements and inverts no others. -/
public theorem model_exists_central_binary_action (C : Subgroup (MulAut Model))
    (hC : IsPGroup 2 C) (hc : Nat.card C = 32) :
    ∃ a : MulAut Model, a ∈ C ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧
      (∀ x : Model, x ^ 2 = 1 → a x = x) ∧
      (∀ b ∈ C, Commute b a) ∧
      (∀ x : Model, a x = x⁻¹ → x ^ 2 = 1) := by
  obtain ⟨z, hz, hne, hCeq⟩ := model_eq_stabilizer_of_card_eq_thirty_two C hC hc
  refine ⟨centralAut z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCeq]
    exact centralAut_fixes_binary z z hz
  · intro heq
    rcases centralAut_nonidentity z with h | h
    · exact h (congrArg (fun a : MulAut Model => a first) heq)
    · exact h (congrArg (fun a : MulAut Model => a second) heq)
  · apply MulEquiv.ext
    exact transvection_invol z
  · exact centralAut_fixes_binary z
  · intro b hb
    rw [hCeq] at hb
    have hh := centralAut_commutes z (b first) (b second) hz hne
      (good_aut b) ((hom_eval b z).symm.trans hb)
    apply hom_ext
    · change b (centralAut z first) = centralAut z (b first)
      rw [hom_eval b]
      exact hh.1.symm
    · change b (centralAut z second) = centralAut z (b second)
      rw [hom_eval b]
      exact hh.2.symm
  · exact centralAut_inverts_only_binary z

/-- Coordinate-free form of the central transvection in a maximal two-action. -/
public theorem exists_central_binary_action {D : Type*} [Group D]
    (model : Nonempty (D ≃* Model)) (C : Subgroup (MulAut D))
    (hC : IsPGroup 2 C) (hc : Nat.card C = 32) :
    ∃ a : MulAut D, a ∈ C ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧
      (∀ x : D, x ^ 2 = 1 → a x = x) ∧
      (∀ b ∈ C, Commute b a) ∧
      (∀ x : D, a x = x⁻¹ → x ^ 2 = 1) := by
  obtain ⟨e⟩ := model
  let F := MulAut.congr e
  have hc' : Nat.card (C.map F.toMonoidHom) = 32 := by
    rwa [Subgroup.card_map_of_injective F.injective]
  obtain ⟨a', ha', hne, hsq, hfix, hcomm, hinv⟩ :=
    model_exists_central_binary_action (C.map F.toMonoidHom) (hC.map _) hc'
  obtain ⟨a, ha, rfl⟩ := ha'
  refine ⟨a, ha, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hne
    simp [h]
  · apply F.injective
    rw [map_pow, map_one]
    exact hsq
  · intro x hx
    apply e.injective
    have hh := hfix (e x) (by rw [← map_pow, hx, map_one])
    simpa [F] using hh
  · intro b hb
    apply Commute.of_map F.injective
    exact hcomm _ (Subgroup.mem_map_of_mem F.toMonoidHom hb)
  · intro x hx
    apply e.injective
    have hh := hinv (e x) (by simpa [F] using congrArg e hx)
    simpa only [map_pow, map_one] using hh


private def beta (z x : Model) : Model :=
  if z = second ^ 2 then (x.1 * x.2 ^ 2, x.2)
  else (x.1, x.2 * x.1 ^ 2)
private def delta (z x : Model) : Model :=
  if z = first ^ 2 then (x.1⁻¹, x.2)
  else if z = second ^ 2 then (x.1, x.2⁻¹)
  else (x.1⁻¹, x.1 ^ 2 * x.2)
private theorem beta_invol : ∀ z x : Model, beta z (beta z x) = x := by decide
private theorem delta_invol : ∀ z x : Model, delta z (delta z x) = x := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem beta_mul : ∀ z x y : Model, beta z (x*y) = beta z x * beta z y := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem delta_mul : ∀ z x y : Model, delta z (x*y) = delta z x * delta z y := by decide
private def betaAut (z : Model) : MulAut Model where
  toFun := beta z
  invFun := beta z
  left_inv := beta_invol z
  right_inv := beta_invol z
  map_mul' := beta_mul z
private def deltaAut (z : Model) : MulAut Model where
  toFun := delta z
  invFun := delta z
  left_inv := delta_invol z
  right_inv := delta_invol z
  map_mul' := delta_mul z
private theorem beta_delta_fix : ∀ z : Model, z ^ 2 = 1 → z ≠ 1 →
    beta z z = z ∧ delta z z = z := by decide
private theorem beta_delta_commute : ∀ z x : Model,
    beta z (delta z x) = delta z (beta z x) := by decide
private theorem transvection_displacement : ∀ z : Model, z ^ 2 = 1 → z ≠ 1 →
    ∀ x : Model, x * (transvection z x)⁻¹ = 1 ∨ x * (transvection z x)⁻¹ = z := by decide
private theorem transvection_norm : ∀ z s : Model, s ^ 2 = 1 →
    ∃ d : Model, d * transvection z d = s := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 4096 in
private theorem lift_obstruction : ∀ z : Model, z ^ 2 = 1 → z ≠ 1 →
    ∀ s d e : Model, transvection z s = s →
      beta z s = d * transvection z d * s →
      delta z s = e * transvection z e * s →
      (beta z e * d = delta z d * e ∨ beta z e * d = delta z d * e * z) →
      s ^ 2 = 1 := by decide

/-- Data witnessing the obstruction to a nonsplit lift of the central
transvection. The two additional actions commute on the base. -/
public theorem model_exists_lift_obstruction (C : Subgroup (MulAut Model))
    (hC : IsPGroup 2 C) (hc : Nat.card C = 32) :
    ∃ a b c : MulAut Model, ∃ z : Model,
      a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧
      (∀ v : Model, v ^ 2 = 1 → a v = v) ∧
      (∀ g ∈ C, Commute g a) ∧
      (∀ v : Model, a v = v⁻¹ → v ^ 2 = 1) ∧ Commute b c ∧
      (∀ v : Model, v * (a v)⁻¹ = 1 ∨ v * (a v)⁻¹ = z) ∧
      (∀ v : Model, v ^ 2 = 1 → ∃ d : Model, d * a d = v) ∧
      (∀ s d e : Model, a s = s → b s = d * a d * s → c s = e * a e * s →
        (b e * d = c d * e ∨ b e * d = c d * e * z) → s ^ 2 = 1) := by
  obtain ⟨z, hz, hne, hCeq⟩ := model_eq_stabilizer_of_card_eq_thirty_two C hC hc
  refine ⟨centralAut z, betaAut z, deltaAut z, z, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, transvection_displacement z hz hne, transvection_norm z, lift_obstruction z hz hne⟩
  · rw [hCeq]
    exact centralAut_fixes_binary z z hz
  · rw [hCeq]
    exact (beta_delta_fix z hz hne).1
  · rw [hCeq]
    exact (beta_delta_fix z hz hne).2
  · intro heq
    rcases centralAut_nonidentity z with h | h
    · exact h (congrArg (fun a : MulAut Model => a first) heq)
    · exact h (congrArg (fun a : MulAut Model => a second) heq)
  · apply MulEquiv.ext
    exact transvection_invol z
  · exact centralAut_fixes_binary z
  · intro b hb
    rw [hCeq] at hb
    have hh := centralAut_commutes z (b first) (b second) hz hne
      (good_aut b) ((hom_eval b z).symm.trans hb)
    apply hom_ext
    · change b (centralAut z first) = centralAut z (b first)
      rw [hom_eval b]
      exact hh.1.symm
    · change b (centralAut z second) = centralAut z (b second)
      rw [hom_eval b]
      exact hh.2.symm
  · exact centralAut_inverts_only_binary z
  · apply MulEquiv.ext
    exact beta_delta_commute z

end C4SquareExtension
