module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.Relations
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-!
# Faithful realization of the eleven-coordinate group

The relations in `ElevenRelations` realize the normal form `x^i y^j z^k`
in an arbitrary group. For collection we use `c = z⁻¹`: the relation becomes
`y*x = c*x*y`, and the central exponent is `(-k : ZMod 11).val`. This equals
the intended `z^k.val` because `z^11 = 1`.

A homomorphism that sends `Z` to an element of order eleven is faithful:
commutators of a kernel element with `Y` and `X` recover its first coordinate
and the negative of its second coordinate as central elements. Those coordinates
vanish, and the remaining central coordinate vanishes as well.

The collection induction adapts the proof in
`Theory.GroupTheory.PGroup.OrderTwentySevenNormalForm`, replacing global
centrality by commutation with the two generators. The presentation convention
and source of the local words are documented in `LocalCertificates.Relations`
and `Elevens.Words` (ATLAS J4G1-max7W1).
-/

namespace Janko4.Simplicity.Elevens
open LocalCoordinates
variable {G : Type*} [Group G]

private lemma swap_powers (x y c : G) (hcx₀ : Commute c x) (hcy₀ : Commute c y)
    (hs : y * x = c * x * y) (j i : ℕ) :
    y ^ j * x ^ i = c ^ (j * i) * x ^ i * y ^ j := by
  have hcx (n m : ℕ) : Commute (c ^ n) (x ^ m) :=
    hcx₀.pow_pow n m
  have hcy (n m : ℕ) : Commute (c ^ n) (y ^ m) :=
    hcy₀.pow_pow n m
  have hs1 (j : ℕ) : y ^ j * x = c ^ j * x * y ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        y ^ (j+1) * x = y ^ j * (y * x) := by group
        _ = y ^ j * (c * x * y) := by rw [hs]
        _ = c * (y ^ j * x) * y := by
          have hh := (hcy 1 j).symm.left_comm (x * y)
          simpa only [pow_one, mul_assoc] using hh
        _ = c * (c ^ j * x * y ^ j) * y := by rw [ih]
        _ = c ^ (j+1) * x * y ^ (j+1) := by rw [pow_succ, pow_succ']; group
  induction i with
  | zero => simp
  | succ i ih =>
    calc
      y ^ j * x ^ (i+1) = (y ^ j * x ^ i) * x := by rw [pow_succ, mul_assoc]
      _ = (c ^ (j*i) * x ^ i * y ^ j) * x := by rw [ih]
      _ = c ^ (j*i) * x ^ i * (c ^ j * x * y ^ j) := by simp only [mul_assoc, hs1]
      _ = (c ^ (j*i) * c ^ j) * (x ^ i * x) * y ^ j := by
        simpa only [mul_assoc] using congrArg (fun z => c ^ (j*i) * z)
          ((hcx j i).symm.left_comm (x * y ^ j))
      _ = c ^ (j*(i+1)) * x ^ (i+1) * y ^ j := by rw [← pow_add, ← pow_succ, Nat.mul_add, Nat.mul_one]

private lemma normal_mul (x y c : G) (hcx₀ : Commute c x) (hcy₀ : Commute c y)
    (hs : y * x = c * x * y) (i j k l m n : ℕ) :
    (x ^ i * y ^ j * c ^ k) * (x ^ l * y ^ m * c ^ n) =
      x ^ (i+l) * y ^ (j+m) * c ^ (k+n+j*l) := by
  have hcx (a b : ℕ) := hcx₀.pow_pow a b
  have hcy (a b : ℕ) := hcy₀.pow_pow a b
  have hcc (a b : ℕ) := (Commute.refl c).pow_pow a b
  calc
    _ = x ^ i * (y ^ j * x ^ l) * y ^ m * (c ^ k * c ^ n) := by
      rw [mul_assoc (x ^ i * y ^ j)]
      rw [show c ^ k * (x ^ l * y ^ m * c ^ n) =
        (x ^ l * y ^ m) * (c ^ k * c ^ n) by
          rw [← mul_assoc, ((hcx k l).mul_right (hcy k m)).eq, mul_assoc]]
      simp only [mul_assoc]
    _ = x ^ i * (c ^ (j*l) * x ^ l * y ^ j) * y ^ m * (c ^ k * c ^ n) := by
      rw [swap_powers x y c hcx₀ hcy₀ hs]
    _ = (x ^ i * x ^ l) * (y ^ j * y ^ m) * ((c ^ k * c ^ n) * c ^ (j*l)) := by
      simp only [mul_assoc]
      have hc := (hcx (j*l) l).mul_right ((hcy (j*l) j).mul_right
        ((hcy (j*l) m).mul_right ((hcc (j*l) k).mul_right (hcc (j*l) n))))
      rw [hc.eq]
      simp only [mul_assoc]
    _ = _ := by simp only [pow_add, mul_assoc]

private lemma pow_val_cast (g : G) (hg : g ^ 11 = 1) (n : ℕ) :
    g ^ (n : ZMod 11).val = g ^ n := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hg]

private lemma pow_val_add (g : G) (hg : g ^ 11 = 1) (a b : ZMod 11) :
    g ^ (a + b).val = g ^ (a.val + b.val) := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hg]

private lemma inverse_coordinate (g : G) (hg : g ^ 11 = 1) (a : ZMod 11) :
    (g⁻¹) ^ (-a).val = g ^ a.val := by
  have h : g ^ a.val * g ^ (-a).val = 1 := by
    rw [← pow_add, ← pow_val_add g hg]
    simp
  rw [inv_pow]
  exact (eq_inv_of_mul_eq_one_left h).symm

private def evaluate (x y z : G) (a : Coord) : G :=
  x ^ a.i.val * y ^ a.j.val * (z⁻¹) ^ (-a.k).val

private lemma evaluate_mul (x y z : G) (h : ElevenRelations x y z) (a b : Coord) :
    evaluate x y z (a * b) = evaluate x y z a * evaluate x y z b := by
  have hc : (z⁻¹) ^ 11 = 1 := by rw [inv_pow, h.z_pow, inv_one]
  have hcx := h.xz.symm.inv_left
  have hcy := h.yz.symm.inv_left
  have hs : y * x = z⁻¹ * x * y := by
    calc
      y * x = x * y * z⁻¹ := by rw [← h.commutator]; group
      _ = z⁻¹ * x * y := by simpa only [mul_assoc] using (hcx.mul_right hcy).eq.symm
  rw [evaluate, evaluate, evaluate,
    normal_mul x y z⁻¹ hcx hcy hs]
  change x ^ (a.i + b.i).val * y ^ (a.j + b.j).val *
    (z⁻¹) ^ (-(a.k + b.k - a.j * b.i)).val = _
  rw [pow_val_add x h.x_pow, pow_val_add y h.y_pow]
  congr 1
  have he : -(a.k + b.k - a.j * b.i) =
      ((-a.k).val + (-b.k).val + a.j.val * b.i.val : ℕ) := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    ring
  rw [he, pow_val_cast _ hc]

private def relationHom (x y z : G) (h : ElevenRelations x y z) : Coord →* G where
  toFun := evaluate x y z
  map_one' := by
    change x ^ (0 : ZMod 11).val * y ^ (0 : ZMod 11).val *
      (z⁻¹) ^ (-(0 : ZMod 11)).val = 1
    simp
  map_mul' := evaluate_mul x y z h

private lemma relationHom_X (x y z : G) (h : ElevenRelations x y z) :
    relationHom x y z h X = x := by
  change evaluate x y z X = x
  simp [evaluate, X, ZMod.val_one_eq_one_mod]

private lemma relationHom_Y (x y z : G) (h : ElevenRelations x y z) :
    relationHom x y z h Y = y := by
  change evaluate x y z Y = y
  simp [evaluate, Y, ZMod.val_one_eq_one_mod]

private lemma relationHom_Z (x y z : G) (h : ElevenRelations x y z) :
    relationHom x y z h Z = z := by
  change evaluate x y z Z = z
  simp only [evaluate, Z, ZMod.val_zero, pow_zero, one_mul]
  rw [inverse_coordinate z h.z_pow]
  simp [ZMod.val_one_eq_one_mod]

private lemma central_coordinate_eq_zero (z : G) (hz : z ^ 11 = 1) (hne : z ≠ 1)
    (f : Coord →* G) (hf : f Z = z) (k : ZMod 11)
    (hk : f ⟨0, 0, k⟩ = 1) : k = 0 := by
  have hp : z ^ k.val = 1 := by
    rw [← hf, ← map_pow, Z_pow]
    simpa using hk
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have ho : orderOf z = 11 := orderOf_eq_prime hz hne
  have hd : 11 ∣ k.val := by
    simpa only [ho] using (orderOf_dvd_iff_pow_eq_one.mpr hp)
  exact (ZMod.val_eq_zero k).mp (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt k))

private lemma coordinate_injective (z : G) (hz : z ^ 11 = 1) (hne : z ≠ 1)
    (f : Coord →* G) (hf : f Z = z) : Function.Injective f := by
  apply (injective_iff_map_eq_one f).mpr
  intro a ha
  have hi : a.i = 0 := by
    apply central_coordinate_eq_zero z hz hne f hf
    have he : a⁻¹ * (Y⁻¹ * a * Y) = ⟨0, 0, a.i⟩ := by
      rw [← actY_eq]
      change cmul (cinv a) (actY a) = _
      apply Coord.ext <;> simp [cmul, cinv, actY]
      ring
    rw [← he]
    simp [ha]
  have hj : a.j = 0 := by
    have hh : -a.j = 0 := by
      apply central_coordinate_eq_zero z hz hne f hf
      have he : a⁻¹ * (X⁻¹ * a * X) = ⟨0, 0, -a.j⟩ := by
        rw [← actX_eq]
        change cmul (cinv a) (actX a) = _
        apply Coord.ext <;> simp [cmul, cinv, actX]
        ring
      rw [← he]
      simp [ha]
    exact neg_eq_zero.mp hh
  have hk : a.k = 0 := by
    apply central_coordinate_eq_zero z hz hne f hf
    have he : a = ⟨0, 0, a.k⟩ := by ext <;> simp [hi, hj]
    rwa [← he]
  change a = cone
  apply Coord.ext <;> simp [cone, hi, hj, hk]

/-- The abstract eleven relations give a faithful realization of the coordinate group,
with the prescribed images of all three generators. -/
public theorem coordinate_embedding_of_relations (x y z : G) (h : ElevenRelations x y z) :
    ∃ f : Coord →* G, Function.Injective f ∧ f X = x ∧ f Y = y ∧ f Z = z := by
  refine ⟨relationHom x y z h, ?_, relationHom_X x y z h,
    relationHom_Y x y z h, relationHom_Z x y z h⟩
  exact coordinate_injective z h.z_pow h.z_ne _ (relationHom_Z x y z h)

end Janko4.Simplicity.Elevens
