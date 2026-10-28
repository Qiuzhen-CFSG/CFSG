module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

/-!
# Cubic collection and rotation identities

If `c * a = a * c * t * p`, the central error `p` is cubic whenever `c` and its
commuting tail `t` are cubic: collect three successive conjugates of `a`.
For six roots with the unitary torus rotation, one nontrivial collection
relation then forces the other three. Applying the rotation twice first
recovers the highest-root relation; applying its inverse recovers the other
short-root coordinate and the second highest-root relation.

The application in `LiftedRelations` takes the quotient by the two actual
cubic defects and instantiates every commutation and rotation hypothesis.
These are the group identities used for Aschbacher--Smith I.1.4(5), printed
p.408, with the unitary conventions of GLS3 §6.1.
-/

public section
open scoped commutatorElement


namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts.LiftedRelations
variable {G : Type*} [Group G]
/-- A central collection error is cubic when the actor and its fixed tail are cubic. -/
theorem collection_error_cube (a c t p : G) (hc : c ^ 3 = 1) (ht : t ^ 3 = 1)
    (hp : p ∈ Subgroup.center G) (hct : Commute c t)
    (h : c * a = a * c * t * p) : p ^ 3 = 1 := by
  have hpc (x : G) : Commute p x := (Subgroup.mem_center_iff.mp hp x).symm
  let k := t * p
  have hck : Commute c k := hct.mul_right (hpc c).symm
  have hca : c * a = a * c * k := by simpa only [k, mul_assoc] using h
  have hn (n : ℕ) : c ^ n * a = a * c ^ n * k ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        c ^ (n + 1) * a = c * (c ^ n * a) := by rw [pow_succ']; group
        _ = c * (a * c ^ n * k ^ n) := by rw [ih]
        _ = (c * a) * c ^ n * k ^ n := by group
        _ = (a * c * k) * c ^ n * k ^ n := by rw [hca]
        _ = a * (c * c ^ n) * (k * k ^ n) := by rw [hck.symm.pow_right n |>.right_comm (a * c)]; group
        _ = a * c ^ (n + 1) * k ^ (n + 1) := by rw [pow_succ', pow_succ']
  have hk : k ^ 3 = 1 := by
    have hh := hn 3
    rw [hc, one_mul, mul_one] at hh
    exact mul_left_cancel (hh.symm.trans (mul_one a).symm)
  simpa only [k, (hpc t).symm.mul_pow, ht, one_mul] using hk

private theorem cubic_sq (x : G) (h : x ^ 3 = 1) : x ^ 2 = x⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, h]
private theorem fourth_relation (a c e v : G)
    (hc : Commute c e) (hcv : Commute c v)
    (hav : Commute a v) (hev : Commute e v) (hv : v ^ 3 = 1)
    (h : c * a = a * c * e⁻¹ * v) (h' : c * a⁻¹ = a⁻¹ * c * e * v) :
    e * a = a * e * v := by
  have h1 : c * a * c⁻¹ = a * e⁻¹ * v := by
    rw [h]
    calc
      a * c * e⁻¹ * v * c⁻¹ = a * (c * (e⁻¹ * v)) * c⁻¹ := by group
      _ = a * ((e⁻¹ * v) * c) * c⁻¹ := by rw [(hc.inv_right.mul_right hcv).eq]
      _ = a * e⁻¹ * v := by group
  have h2 : c * a⁻¹ * c⁻¹ = a⁻¹ * e * v := by
    rw [h']
    calc
      a⁻¹ * c * e * v * c⁻¹ = a⁻¹ * (c * (e * v)) * c⁻¹ := by group
      _ = a⁻¹ * ((e * v) * c) * c⁻¹ := by rw [(hc.mul_right hcv).eq]
      _ = a⁻¹ * e * v := by group
  have h3 : a * e⁻¹ * v = v⁻¹ * e⁻¹ * a := by
    calc
      a * e⁻¹ * v = c * a * c⁻¹ := h1.symm
      _ = (c * a⁻¹ * c⁻¹)⁻¹ := by group
      _ = (a⁻¹ * e * v)⁻¹ := by rw [h2]
      _ = v⁻¹ * e⁻¹ * a := by group
  apply mul_right_cancel (b := e⁻¹ * v ^ 2)
  calc
    e * a * (e⁻¹ * v ^ 2) = e * v * (a * e⁻¹ * v) := by
      simp only [← mul_assoc, pow_two]
      rw [hav.symm.right_comm e]
      exact congrArg (· * v) ((hev.inv_left).right_comm (e * a))
    _ = e * v * (v⁻¹ * e⁻¹ * a) := by rw [h3]
    _ = a := by group
    _ = a * e * v * (e⁻¹ * v ^ 2) := by
      rw [hev.right_comm a, mul_assoc, mul_assoc, mul_inv_cancel_left,
        ← pow_succ', hv, mul_one]

private theorem invert_actor (c a k : G) (hck : Commute c k)
    (h : c * a = a * c * k) : c⁻¹ * a = a * c⁻¹ * k⁻¹ := by
  apply (mul_left_cancel (a := c))
  calc
    c * (c⁻¹ * a) = a := by group
    _ = c * (a * c⁻¹ * k⁻¹) := by
      rw [← mul_assoc, ← mul_assoc, h, hck.right_comm a]
      group

/-- One collection relation and the marked rotation force the other three tails. -/
theorem remaining_three_relations (a b c d e v : G) (φ : G ≃* G)
    (ha : φ a = b⁻¹) (hb : φ b = a) (hc : φ c = c⁻¹)
    (hd : φ d = e) (he : φ e = d⁻¹) (hv : φ v = v⁻¹)
    (he3 : e ^ 3 = 1) (hv3 : v ^ 3 = 1)
    (hce : Commute c e) (hcv : Commute c v)
    (hav : Commute a v) (hev : Commute e v)
    (h02 : c * a = a * c * e ^ 2 * v) :
    e * a = a * e * v ∧ c * b = b * c * d * v ∧ d * b = b * d * v ^ 2 := by
  have h : c * a = a * c * e⁻¹ * v := by simpa only [cubic_sq e he3] using h02
  have h' : c * a⁻¹ = a⁻¹ * c * e * v := by
    have hh := congrArg φ (congrArg φ h)
    simpa only [map_mul, map_inv, ha, hb, hc, hd, he, hv, inv_inv] using hh
  have h04 := fourth_relation a c e v hce hcv hav hev hv3 h h'
  refine ⟨h04, ?_, ?_⟩
  · apply φ.injective
    simp only [map_mul, hb, hc, hd, hv]
    have hi := invert_actor c a (e⁻¹ * v) (hce.inv_right.mul_right hcv)
      (by simpa only [mul_assoc] using h)
    simpa only [mul_inv_rev, inv_inv, ← hev.inv_right.eq, mul_assoc] using hi
  · apply φ.injective
    simpa only [map_mul, map_pow, map_inv, hb, hd, hv, inv_pow, cubic_sq v hv3, inv_inv] using h04
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts.LiftedRelations
