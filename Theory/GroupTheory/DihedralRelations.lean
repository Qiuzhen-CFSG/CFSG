module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Group.Conj

/-!
# Evaluation of the dihedral relations

The rotation and reflection relations define a homomorphism from the dihedral
group. Explicit evaluation equations retain the chosen generators, as needed
for computable semidirect-product models of rank-two parabolics. This exposes
the same elementary construction used privately in `DihedralPresentation`.
-/

@[expose] public section
namespace Theory.GroupTheory.DihedralRelations

def rotation {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c : G) (hc : c ^ m = 1) : Multiplicative (ZMod m) →* G where
  toFun i := c ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change c ^ (i.toAdd + j.toAdd).val = c ^ i.toAdd.val * c ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod (i.toAdd.val + j.toAdd.val) hc).symm

theorem rotation_one {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c : G) (hc : c ^ m = 1) : rotation c hc (.ofAdd 1) = c := by
  change c ^ (1 : ZMod m).val = c
  rw [← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod 1 hc, pow_one]

def ofRelations {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c d : G) (hc : c ^ m = 1) (hd : d ^ 2 = 1)
    (hconj : d * c * d⁻¹ = c⁻¹) : DihedralGroup m →* G := by
  let f := rotation c hc
  have hswap (i : Multiplicative (ZMod m)) : f i * d = d * (f i)⁻¹ := by
    have hh : d * f i * d⁻¹ = (f i)⁻¹ := by
      change d * c ^ i.toAdd.val * d⁻¹ = (c ^ i.toAdd.val)⁻¹
      rw [← conj_pow, hconj, inv_pow]
    have dd : d * d = 1 := by simpa [pow_two] using hd
    calc
      f i * d = (d * d) * f i * d := by rw [dd, one_mul]
      _ = d * (d * f i * d⁻¹) := by
        have hi : d⁻¹ = d := inv_eq_of_mul_eq_one_right dd
        rw [hi]
        simp only [mul_assoc]
      _ = d * (f i)⁻¹ := by rw [hh]
  refine {
    toFun := fun x => match x with
      | .r i => f (.ofAdd i)
      | .sr i => d * f (.ofAdd i)
    map_one' := by change f 1 = 1; exact f.map_one
    map_mul' := ?_ }
  intro x y
  cases x with
  | r i =>
    cases y with
    | r j => exact f.map_mul (.ofAdd i) (.ofAdd j)
    | sr j =>
      change d * f (.ofAdd (j - i)) = f (.ofAdd i) * (d * f (.ofAdd j))
      rw [← mul_assoc, hswap, mul_assoc]
      rw [sub_eq_add_neg]
      change d * f ((.ofAdd j) * (.ofAdd i)⁻¹) = d * ((f (.ofAdd i))⁻¹ * f (.ofAdd j))
      rw [map_mul, map_inv]
      congr 1
      simpa only [map_inv] using (Commute.map (Commute.all (.ofAdd j) ((.ofAdd i)⁻¹)) f).eq
  | sr i =>
    cases y with
    | r j =>
      change d * f ((.ofAdd i) * (.ofAdd j)) = d * f (.ofAdd i) * f (.ofAdd j)
      rw [map_mul, mul_assoc]
    | sr j =>
      change f (.ofAdd (j - i)) = (d * f (.ofAdd i)) * (d * f (.ofAdd j))
      rw [mul_assoc d, ← mul_assoc (f (.ofAdd i)), hswap, ← mul_assoc d, ← mul_assoc d d]
      have dd : d * d = 1 := by simpa [pow_two] using hd
      rw [dd, one_mul]
      rw [sub_eq_add_neg]
      change f ((.ofAdd j) * (.ofAdd i)⁻¹) = (f (.ofAdd i))⁻¹ * f (.ofAdd j)
      rw [map_mul, map_inv]
      simpa only [map_inv] using (Commute.map (Commute.all (.ofAdd j) ((.ofAdd i)⁻¹)) f).eq


@[simp] theorem ofRelations_r {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c d : G) (hc : c ^ m = 1) (hd : d ^ 2 = 1)
    (hconj : d*c*d⁻¹=c⁻¹) (i : ZMod m) :
    ofRelations c d hc hd hconj (.r i) = c ^ i.val := rfl

@[simp] theorem ofRelations_sr {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c d : G) (hc : c ^ m = 1) (hd : d ^ 2 = 1)
    (hconj : d*c*d⁻¹=c⁻¹) (i : ZMod m) :
    ofRelations c d hc hd hconj (.sr i) = d * c ^ i.val := rfl

end Theory.GroupTheory.DihedralRelations
