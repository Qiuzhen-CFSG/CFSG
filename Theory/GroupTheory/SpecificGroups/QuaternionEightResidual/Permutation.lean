module
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut

/-!
# The four-diagonal permutation representation of Aut(Q₈)

Automorphisms permute the three quaternion axes with signs. Their action on
body diagonals of the cube gives a faithful permutation representation on four
points; the known order twenty-four makes it an isomorphism with S₄.
The four diagonals are represented by `(i, ±j, ±ij)`, modulo simultaneous sign
change. The finite calculations use the same generator-pair encoding as
`QuaternionEightAut`, and are checked by the kernel.

This is the automorphism identification used in Aschbacher–Smith,
Lemma 14.2.21, printed p.988.
-/

namespace QuaternionGroup.Residual
private abbrev Q := QuaternionGroup 2
private abbrev A := MulAut Q
private def goodPair (p : Q × Q) : Prop :=
  p.1 ^ 2 = a 2 ∧ p.2 ^ 2 = a 2 ∧ p.1 * p.2 ≠ p.2 * p.1
private instance : DecidablePred goodPair := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private abbrev Pairs := {p : Q × Q // goodPair p}
private def pairMap (p : Q × Q) : Q → Q
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val

private def diagonal (n : Fin 4) : Q × Q × Q :=
  (a 1, if n.val < 2 then xa 0 else xa 2,
    if n.val % 2 = 0 then xa 3 else xa 1)
private def encode (t : Q × Q × Q) : Fin 4 :=
  let si := a 1 = t.1 ∨ a 1 = t.2.1 ∨ a 1 = t.2.2
  let sj := xa 0 = t.1 ∨ xa 0 = t.2.1 ∨ xa 0 = t.2.2
  let sk := xa 3 = t.1 ∨ xa 3 = t.2.1 ∨ xa 3 = t.2.2
  if si ↔ sj then (if si ↔ sk then 0 else 1) else (if si ↔ sk then 2 else 3)
private def act (f : Q → Q) (n : Fin 4) : Fin 4 :=
  encode (f (diagonal n).1, f (diagonal n).2.1, f (diagonal n).2.2)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem table_mul : ∀ p q : Pairs, ∀ n : Fin 4,
    act (fun x => pairMap p.val (pairMap q.val x)) n =
      act (pairMap p.val) (act (pairMap q.val) n) := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem table_inj : ∀ p q : Pairs,
    (∀ n : Fin 4, act (pairMap p.val) n = act (pairMap q.val) n) →
    p.val = q.val := by decide

private theorem square_of_square_ne_one : ∀ x : Q, x^2 ≠ 1 → x^2=a 2 := by decide
private def autPair (e : A) : Pairs := by
  refine ⟨(e (a 1), e (xa 0)), ?_, ?_, ?_⟩
  · apply square_of_square_ne_one
    intro h
    have hi : (a 1 : Q)^2 ≠ 1 := by decide
    apply hi
    apply e.injective
    simpa only [map_pow,map_one] using h
  · apply square_of_square_ne_one
    intro h
    have hi : (xa 0 : Q)^2 ≠ 1 := by decide
    apply hi
    apply e.injective
    simpa only [map_pow,map_one] using h
  · intro h
    have hi : (a 1 : Q)*xa 0 ≠ xa 0*a 1 := by decide
    apply hi
    apply e.injective
    simpa only [map_mul] using h

private theorem pairMap_autPair (e : A) : pairMap (autPair e).val = (e : Q → Q) := by
  funext x
  cases x with
  | a i =>
    change (e (a 1))^i.val=e (a i)
    rw [←map_pow,a_one_pow,ZMod.natCast_zmod_val]
  | xa i =>
    change e (xa 0)*(e (a 1))^i.val=e (xa i)
    rw [←map_pow,←map_mul,a_one_pow,ZMod.natCast_zmod_val,xa_mul_a,zero_add]

private theorem act_mul (e f : A) (n : Fin 4) :
    act (e * f : A) n = act e (act f n) := by
  have h := table_mul (autPair e) (autPair f) n
  simpa only [pairMap_autPair, act, MulAut.mul_apply] using h

private theorem act_one : ∀ n : Fin 4, act (1 : A) n = n := by decide

private def autPerm (e : A) : Equiv.Perm (Fin 4) where
  toFun := act e
  invFun := act (e⁻¹ : A)
  left_inv n := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv n := by rw [← act_mul, mul_inv_cancel, act_one]

private def autPermHom : A →* Equiv.Perm (Fin 4) where
  toFun := autPerm
  map_one' := by apply Equiv.ext; exact act_one
  map_mul' e f := by apply Equiv.ext; exact act_mul e f

private theorem autPermHom_injective : Function.Injective autPermHom := by
  intro e f h
  have hp : (autPair e).val = (autPair f).val := table_inj _ _ (by
    intro n
    rw [pairMap_autPair, pairMap_autPair]
    exact DFunLike.congr_fun h n)
  ext x
  rw [← pairMap_autPair e, ← pairMap_autPair f, hp]

/-- The faithful action on the four cube diagonals identifies Aut(Q₈) with S₄. -/
public noncomputable def autEquivPerm : MulAut (QuaternionGroup 2) ≃* Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective autPermHom ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨autPermHom_injective, by
      rw [QuaternionGroup.card_mulAut_two, Nat.card_eq_fintype_card]
      decide⟩)

end QuaternionGroup.Residual
