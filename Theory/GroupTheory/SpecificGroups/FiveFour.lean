module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.Prod
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The faithful five-by-four semidirect product

The generator of the cyclic group of order four acts on the cyclic group
of order five by squaring. The universal homomorphism below takes its two
specified generators to any elements satisfying the corresponding power
and conjugation relations. This is the usual presentation of `C₅ : C₄`.
-/

@[expose] public section
namespace FiveFour

abbrev Cyclic (n : ℕ) := Multiplicative (ZMod n)

def generator (n : ℕ) : Cyclic n := Multiplicative.ofAdd 1

/-- Evaluation of a finite cyclic generator at an element whose power is one. -/
def cyclicHom {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (x : G) (hx : x ^ n = 1) : Cyclic n →* G where
  toFun t := x ^ t.toAdd.val
  map_one' := by simp
  map_mul' s t := by
    change x ^ (s.toAdd + t.toAdd).val = x ^ s.toAdd.val * x ^ t.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

theorem generator_pow_val {n : ℕ} [NeZero n] (t : Cyclic n) :
    generator n ^ t.toAdd.val = t := by
  apply Multiplicative.toAdd.injective
  simp [generator, toAdd_pow, nsmul_eq_mul]

@[simp] theorem cyclicHom_generator {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (x : G) (hx : x ^ n = 1) : cyclicHom x hx (generator n) = x := by
  change x ^ (1 : ZMod n).val = x
  rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hx, pow_one]

/-- Maps out of a finite cyclic group are determined by the standard generator. -/
theorem cyclicHom_ext {G : Type*} [Group G] {n : ℕ} [NeZero n]
    {f g : Cyclic n →* G} (h : f (generator n) = g (generator n)) : f = g := by
  apply MonoidHom.ext
  intro t
  rw [← generator_pow_val t, map_pow, map_pow, h]

/-- Squaring on the cyclic group of order five. -/
def doubling : MulAut (Cyclic 5) where
  toFun t := Multiplicative.ofAdd (2 * t.toAdd)
  invFun t := Multiplicative.ofAdd (3 * t.toAdd)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

theorem doubling_four : doubling ^ 4 = 1 := by
  apply MulEquiv.ext
  intro t
  exact (by decide +kernel : ∀ t : Cyclic 5, (doubling ^ 4) t = t) t

/-- The faithful action defining the semidirect product. -/
def action : Cyclic 4 →* MulAut (Cyclic 5) := cyclicHom doubling doubling_four

theorem action_injective : Function.Injective action := by
  have h : Function.Injective (fun t : Cyclic 4 => action t (generator 5)) := by
    decide +kernel
  exact fun s t hst => h (congrArg (fun f : MulAut (Cyclic 5) => f (generator 5)) hst)

abbrev Group := SemidirectProduct (Cyclic 5) (Cyclic 4) action

def c : Group := SemidirectProduct.inl (generator 5)
def a : Group := SemidirectProduct.inr (generator 4)

instance : Fintype Group := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

theorem card : Nat.card Group = 20 := by
  rw [SemidirectProduct.card]
  change Nat.card (ZMod 5) * Nat.card (ZMod 4) = 20
  simp

theorem c_five : c ^ 5 = 1 := by decide +kernel
theorem a_four : a ^ 4 = 1 := by decide +kernel
theorem a_conj_c : a * c * a⁻¹ = c ^ 2 := by decide +kernel

/-- The ordered cyclic coordinates give the normal form. -/
theorem normal_form (g : Group) : c ^ g.left.toAdd.val * a ^ g.right.toAdd.val = g := by
  simp only [c, a, ← map_pow, generator_pow_val, SemidirectProduct.inl_left_mul_inr_right]

theorem lift_compatible {G : Type*} [_root_.Group G] (c a : G)
    (hc : c ^ 5 = 1) (ha : a ^ 4 = 1) (h : a * c * a⁻¹ = c ^ 2)
    (t : Cyclic 4) :
    (cyclicHom c hc).comp (action t).toMonoidHom =
      (MulAut.conj (cyclicHom a ha t)).toMonoidHom.comp (cyclicHom c hc) := by
  have hgen : (cyclicHom c hc).comp doubling.toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (cyclicHom c hc) := by
    apply cyclicHom_ext
    change cyclicHom c hc (doubling (generator 5)) = _
    have hd : doubling (generator 5) = generator 5 ^ 2 := by decide +kernel
    rw [hd, map_pow, cyclicHom_generator]
    simpa using h.symm
  have hp (k : ℕ) : (cyclicHom c hc).comp (doubling ^ k).toMonoidHom =
      (MulAut.conj (a ^ k)).toMonoidHom.comp (cyclicHom c hc) := by
    induction k with
    | zero => apply MonoidHom.ext; intro x; simp
    | succ k ih =>
      apply MonoidHom.ext
      intro x
      have hk := DFunLike.congr_fun ih (doubling x)
      have h1 := DFunLike.congr_fun hgen x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hk h1 ⊢
      rw [pow_succ, MulAut.mul_apply, hk, h1, pow_succ, map_mul, MulAut.mul_apply]
  exact hp t.toAdd.val

/-- The universal map for the relations `c⁵ = a⁴ = 1`, `aca⁻¹ = c²`. -/
def lift {G : Type*} [_root_.Group G] (c a : G)
    (hc : c ^ 5 = 1) (ha : a ^ 4 = 1) (h : a * c * a⁻¹ = c ^ 2) : Group →* G :=
  SemidirectProduct.lift (cyclicHom c hc) (cyclicHom a ha) (lift_compatible c a hc ha h)

@[simp] theorem lift_c {G : Type*} [_root_.Group G] (c a : G)
    (hc : c ^ 5 = 1) (ha : a ^ 4 = 1) (h : a * c * a⁻¹ = c ^ 2) :
    lift c a hc ha h FiveFour.c = c := by
  simp [lift, FiveFour.c]

@[simp] theorem lift_a {G : Type*} [_root_.Group G] (c a : G)
    (hc : c ^ 5 = 1) (ha : a ^ 4 = 1) (h : a * c * a⁻¹ = c ^ 2) :
    lift c a hc ha h FiveFour.a = a := by
  simp [lift, FiveFour.a]

@[ext] theorem hom_ext {G : Type*} [_root_.Group G] {f g : Group →* G}
    (hc : f c = g c) (ha : f a = g a) : f = g := by
  apply MonoidHom.ext
  intro x
  rw [← normal_form x, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hc, ha]

/-- Exact orders of the two generator images suffice for faithful recognition. -/
theorem lift_injective {G : Type*} [_root_.Group G] (c a : G)
    (hc : c ^ 5 = 1) (ha : a ^ 4 = 1) (h : a * c * a⁻¹ = c ^ 2)
    (oc : orderOf c = 5) (oa : orderOf a = 4) :
    Function.Injective (lift c a hc ha h) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  change c ^ g.left.toAdd.val * a ^ g.right.toAdd.val = 1 at hg
  have he : c ^ g.left.toAdd.val = (a ^ g.right.toAdd.val)⁻¹ :=
    eq_inv_of_mul_eq_one_left hg
  have h4 : (c ^ g.left.toAdd.val) ^ 4 = 1 := by
    rw [he, inv_pow, pow_right_comm, ha, one_pow, inv_one]
  have h5 : (c ^ g.left.toAdd.val) ^ 5 = 1 := by
    rw [pow_right_comm, hc, one_pow]
  have hc0 : c ^ g.left.toAdd.val = 1 := by
    simpa only [show 5 = 4 + 1 from rfl, pow_succ, h4, one_mul] using h5
  have ha0 : a ^ g.right.toAdd.val = 1 := by simpa only [hc0, one_mul] using hg
  have hl : g.left.toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt
    (by simpa only [oc] using orderOf_dvd_of_pow_eq_one hc0) (ZMod.val_lt _)
  have hr : g.right.toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt
    (by simpa only [oa] using orderOf_dvd_of_pow_eq_one ha0) (ZMod.val_lt _)
  rw [← normal_form g, hl, hr, pow_zero, pow_zero, one_mul]

/-- The involution used alongside the four-element generator. -/
def r : Group := a ^ 2 * c

theorem r_two : r ^ 2 = 1 := by decide +kernel

theorem c_eq : c = a ^ 2 * r := by decide +kernel

end FiveFour
