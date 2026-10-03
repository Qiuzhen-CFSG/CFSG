module

public import Theory.GroupTheory.PGroup.NormalEightNormLifting
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Norm control for a cyclic two-group times a cyclic four-group

For V = C_(2^n) × C₄ with n ≥ 3, consider automorphisms fixing
all squares and whose displacement on fourth roots lies in the highest
nontrivial power image. This intrinsic description gives a normal
automorphism subgroup. Its actions commute and invert only involutions.
The norm map from fourth roots to involutions is surjective: its kernel
embeds in the four involutions, whereas the fourth-root subgroup has order
sixteen. This avoids choosing the eight individual coordinate matrices.

The construction is the coordinate norm-control argument associated with
MacWilliams, *On 2-groups with no normal abelian subgroups of rank 3*,
Trans. AMS 150 (1970), §1.2. The proofs are direct power-kernel calculations.
-/

open Subgroup
namespace UnequalCyclicFourNormControl
public abbrev V (n : ℕ) := Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 4)
public abbrev A (n : ℕ) := Multiplicative (ZMod (2 ^ n))
public abbrev C4 := Multiplicative (ZMod 4)

@[expose] public def longLine (n : ℕ) : Subgroup (V n) := (powMonoidHom (2 ^ (n-1))).range

public theorem longLine_characteristic (n : ℕ) : (longLine n).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro f
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨f z, (map_pow f z _).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(f.symm y) ^ (2^(n-1)), ⟨f.symm y, rfl⟩, by simp⟩

@[expose] public def controlSubgroup (n : ℕ) : Subgroup (MulAut (V n)) where
  carrier := {f | (∀ x, f (x^2) = x^2) ∧
    ∀ x, x^4 = 1 → f x * x⁻¹ ∈ longLine n}
  one_mem' := by
    refine ⟨fun x => rfl, ?_⟩
    intro x _
    change x * x⁻¹ ∈ longLine n
    simp only [mul_inv_cancel, Subgroup.one_mem]
  mul_mem' := by
    rintro f g ⟨hf, hfL⟩ ⟨hg, hgL⟩
    refine ⟨fun x => by change f (g (x^2)) = _; rw [hg, hf], ?_⟩
    intro x hx
    have hfx := hfL (g x) (by rw [← map_pow, hx, map_one])
    have hgx := hgL x hx
    change f (g x) * x⁻¹ ∈ longLine n
    simpa [mul_assoc] using (longLine n).mul_mem hfx hgx
  inv_mem' := by
    rintro f ⟨hf, hfL⟩
    refine ⟨?_, ?_⟩
    · intro x
      apply f.injective
      change f (f.symm (x^2)) = f (x^2)
      rw [f.apply_symm_apply, hf]
    · intro x hx
      have hs : (f.symm x)^4 = 1 := by rw [← map_pow, hx, map_one]
      have h := (longLine n).inv_mem (hfL (f.symm x) hs)
      simpa using h

public theorem mem_controlSubgroup (n : ℕ) (f : MulAut (V n)) :
    f ∈ controlSubgroup n ↔ (∀ x, f (x^2) = x^2) ∧
      ∀ x, x^4 = 1 → f x * x⁻¹ ∈ longLine n := Iff.rfl

public theorem controlSubgroup_normal (n : ℕ) : (controlSubgroup n).Normal := by
  let := longLine_characteristic n
  constructor
  rintro t ⟨ht, htL⟩ f
  refine ⟨?_, ?_⟩
  · intro x
    change f (t (f.symm (x^2))) = x^2
    rw [map_pow, ht, ← map_pow, f.apply_symm_apply]
  · intro x hx
    have hs : (f.symm x)^4 = 1 := by rw [← map_pow, hx, map_one]
    have h := (Subgroup.characteristic_iff_le_comap.mp
      (longLine_characteristic n) f) (htL (f.symm x) hs)
    change f (t (f.symm x)) * x⁻¹ ∈ longLine n
    change f (t (f.symm x) * (f.symm x)⁻¹) ∈ longLine n at h
    simpa only [map_mul, map_inv, f.apply_symm_apply] using h

public theorem roots_le_squares (n : ℕ) (hn : 3 ≤ n) :
    (powMonoidHom 4 : A n →* A n).ker ≤ (powMonoidHom 2).range := by
  have hp : 2 ^ (n-2) * 4 = 2 ^ n := by
    rw [show 4 = 2^2 from rfl, ← pow_add]
    congr 1
    omega
  have he : (powMonoidHom (2^(n-2)) : A n →* A n).range =
      (powMonoidHom 4).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro x ⟨y, rfl⟩
      change (y ^ (2^(n-2))) ^ 4 = 1
      rw [← pow_mul, hp]
      simpa using pow_card_eq_one' (x := y)
    · rw [IsCyclic.card_powMonoidHom_range, IsCyclic.card_powMonoidHom_ker]
      have hd : 2^(n-2) ∣ 2^n := pow_dvd_pow 2 (by omega)
      have hd4 : 4 ∣ 2^n := by rw [← hp]; exact dvd_mul_left _ _
      simp only [A, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
        Nat.gcd_eq_right hd, Nat.gcd_eq_right hd4]
      rw [← hp, Nat.mul_div_right _ (by positivity)]
  rw [← he]
  rintro x ⟨y, rfl⟩
  refine ⟨y ^ (2^(n-3)), ?_⟩
  change (y ^ (2^(n-3))) ^ 2 = y ^ (2^(n-2))
  rw [← pow_mul, ← pow_succ]
  congr 2
  omega

private theorem C4_roots_le_squares (x : C4) (hx : x^2 = 1) :
    ∃ y : C4, y^2 = x := by
  have he : (powMonoidHom 2 : C4 →* C4).range = (powMonoidHom 2).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro z ⟨y, rfl⟩
      change (y^2)^2 = 1
      simpa [← pow_mul] using pow_card_eq_one' (x := y)
    · rw [IsCyclic.card_powMonoidHom_range, IsCyclic.card_powMonoidHom_ker]
      norm_num [C4]
  change x ∈ (powMonoidHom 2 : C4 →* C4).range
  rw [he]
  exact hx

private theorem square_one_has_root (n : ℕ) (hn : 3 ≤ n) (x : V n) (hx : x^2 = 1) :
    ∃ y : V n, y^2 = x := by
  have hx4 : x^4 = 1 := by
    calc x^4 = (x^2)^2 := pow_mul x 2 2
         _ = 1 := by rw [hx, one_pow]
  obtain ⟨a, ha⟩ := roots_le_squares n hn (congrArg Prod.fst hx4)
  obtain ⟨b, hb⟩ := C4_roots_le_squares x.2 (congrArg Prod.snd hx)
  exact ⟨(a,b), Prod.ext ha hb⟩

private theorem fixes_square_one (n : ℕ) (hn : 3 ≤ n) (f : MulAut (V n))
    (hf : f ∈ controlSubgroup n) (x : V n) (hx : x^2 = 1) : f x = x := by
  obtain ⟨y, rfl⟩ := square_one_has_root n hn x hx
  exact hf.1 y

public theorem control_commute (n : ℕ) (hn : 3 ≤ n) (f g : MulAut (V n))
    (hf : f ∈ controlSubgroup n) (hg : g ∈ controlSubgroup n) : Commute f g := by
  have hdis (a : MulAut (V n)) (ha : a ∈ controlSubgroup n) (x : V n) :
      (a x * x⁻¹)^2 = 1 := by
    rw [mul_pow, inv_pow, ← map_pow, ha.1, mul_inv_cancel]
  apply MulEquiv.ext
  intro x
  have hfg := fixes_square_one n hn f hf _ (hdis g hg x)
  have hgf := fixes_square_one n hn g hg _ (hdis f hf x)
  change f (g x) = g (f x)
  rw [map_mul, map_inv] at hfg hgf
  calc
    f (g x) = (g x * x⁻¹) * f x := by rw [← hfg]; simp
    _ = (f x * x⁻¹) * g x := by ac_rfl
    _ = g (f x) := by rw [← hgf]; simp

public theorem longLine_snd (n : ℕ) (hn : 3 ≤ n) (x : V n)
    (hx : x ∈ longLine n) : x.2 = 1 := by
  obtain ⟨y, rfl⟩ := hx
  change y.2 ^ (2^(n-1)) = 1
  have hd : 4 ∣ 2^(n-1) := by
    change 2^2 ∣ 2^(n-1)
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨k, hk⟩ := hd
  rw [hk, pow_mul, show y.2^4 = 1 by simpa using pow_card_eq_one' (x := y.2), one_pow]

public theorem control_inverted (n : ℕ) (hn : 3 ≤ n) (f : MulAut (V n))
    (hf : f ∈ controlSubgroup n) (x : V n) (hx : f x = x⁻¹) : x^2 = 1 := by
  have hs : (x^2)^2 = 1 := by
    have h := hf.1 x
    rw [map_pow, hx, inv_pow] at h
    calc
      _ = (x^2)⁻¹ * x^2 := by rw [h, pow_two]
      _ = 1 := inv_mul_cancel _
  have hx4 : x^4 = 1 := by simpa [← pow_mul] using hs
  have hl := longLine_snd n hn _ (hf.2 x hx4)
  have hb : x.2^2 = 1 := by
    change (f x).2 * x.2⁻¹ = 1 at hl
    rw [hx] at hl
    have hh : (x.2^2)⁻¹ = 1 := by simpa [pow_two] using hl
    exact inv_eq_one.mp hh
  obtain ⟨a, ha⟩ := roots_le_squares n hn (congrArg Prod.fst hx4)
  obtain ⟨b, hb⟩ := C4_roots_le_squares x.2 hb
  have hr : (a,b)^2 = x := Prod.ext ha hb
  have hfix : f x = x := hr ▸ hf.1 (a,b)
  calc
    x^2 = f x * x := by rw [hfix, pow_two]
    _ = 1 := by rw [hx, inv_mul_cancel]
private theorem card_roots (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : k ≤ 2) :
    Nat.card (powMonoidHom (2^k) : V n →* V n).ker = 2^k * 2^k := by
  have he : (powMonoidHom (2^k) : V n →* V n).ker =
      (powMonoidHom (2^k) : A n →* A n).ker.prod
        (powMonoidHom (2^k) : C4 →* C4).ker := by
    ext x
    exact Prod.ext_iff
  rw [he, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_ker]
  have hd : 2^k ∣ 2^n := pow_dvd_pow 2 (by omega)
  have h4d : 2^k ∣ 4 := pow_dvd_pow 2 hk
  simp [Nat.gcd_eq_right hd, Nat.gcd_eq_right h4d]

public theorem control_norm (n : ℕ) (hn : 3 ≤ n) (f : MulAut (V n))
    (hf : f ∈ controlSubgroup n) (x : V n) (hx : x^2 = 1) :
    ∃ y : V n, y * f y = x := by
  let K4 : Subgroup (V n) := (powMonoidHom 4).ker
  let K2 : Subgroup (V n) := (powMonoidHom 2).ker
  let N : K4 →* K2 :=
    { toFun := fun y => ⟨(y : V n) * f y, by
        change ((y : V n) * f y)^2 = 1
        rw [mul_pow, ← map_pow, hf.1, ← pow_two, ← pow_mul]
        exact y.property⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro y z
        apply Subtype.ext
        change ((y : V n) * z) * f ((y : V n) * z) =
          ((y : V n) * f y) * ((z : V n) * f z)
        rw [map_mul]
        ac_rfl }
  have hker : Nat.card N.ker ≤ 4 := by
    let j : N.ker → K2 := fun y => ⟨((y : K4) : V n), by
      apply control_inverted n hn f hf
      have he : ((y : K4) : V n) * f ((y : K4) : V n) = 1 :=
        congrArg Subtype.val y.property
      exact eq_inv_of_mul_eq_one_right he⟩
    have hj : Function.Injective j := by
      intro y z hyz
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : K2 => (w : V n)) hyz
    exact (Nat.card_le_card_of_injective j hj).trans_eq (card_roots n hn 1 (by decide))
  have hsurj : Function.Surjective N := by
    apply N.surjective_of_card_ker_le_div
    have h4 : Nat.card K4 = 16 := card_roots n hn 2 (by decide)
    have h2 : Nat.card K2 = 4 := card_roots n hn 1 (by decide)
    rw [h4, h2]
    exact hker
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  exact ⟨y, congrArg Subtype.val hy⟩

@[expose] public def control (n : ℕ) (hn : 3 ≤ n) : InvolutionNormControl (V n) where
  subgroup := controlSubgroup n
  conj_mem f _ t ht := (controlSubgroup_normal n).conj_mem t ht f
  commute f hf g hg := control_commute n hn f g hf hg
  inverted f hf x hx := control_inverted n hn f hf x hx
  norm f hf x hx := control_norm n hn f hf x hx

/-- The subgroup of automorphisms fixing every element of square one. -/
@[expose] public def involutionFixing (n : ℕ) : Subgroup (MulAut (V n)) where
  carrier := {f | ∀ x, x^2 = 1 → f x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by
    intro f g hf hg x hx
    change f (g x) = x
    rw [hg x hx, hf x hx]
  inv_mem' := by
    intro f hf x hx
    apply f.injective
    change f (f.symm x) = f x
    rw [f.apply_symm_apply, hf x hx]

/-- The long cyclic factor's standard generator. -/
@[expose] public def longGenerator (n : ℕ) : V n := (Multiplicative.ofAdd 1, 1)

/-- The cyclic four factor's standard generator. -/
@[expose] public def shortGenerator (n : ℕ) : V n := (1, Multiplicative.ofAdd 1)

/-- The two diagonal coordinates, reduced modulo four. Multiplicativity on
involution-fixing automorphisms and control of the involutive kernel are
separate coordinate facts. -/
@[expose] public def diagonal (n : ℕ) (hn : 3 ≤ n) (f : MulAut (V n)) :
    ZMod 4 × ZMod 4 :=
  ((ZMod.castHom (show 4 ∣ 2^n from pow_dvd_pow 2 (show 2 ≤ n by omega)) (ZMod 4))
    (f (longGenerator n)).1.toAdd, (f (shortGenerator n)).2.toAdd)

@[simp] public theorem diagonal_one (n : ℕ) (hn : 3 ≤ n) :
    diagonal n hn 1 = 1 := by
  apply Prod.ext
  · exact map_one (ZMod.castHom
      (show 4 ∣ 2^n from pow_dvd_pow 2 (show 2 ≤ n by omega)) (ZMod 4))
  · rfl

end UnequalCyclicFourNormControl
