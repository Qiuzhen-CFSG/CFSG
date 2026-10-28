module

public import Theory.SpecificGroups.ExoticTwoGroup.ExtensionFrame
public import Theory.GroupTheory.PGroup.Omega
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic

/-!
# Algebraic correction of exotic extension lifts

An action frame over a self-centralizing abelian base determines the outer
squares and conjugation defects modulo that base. The inversion lift inverts
the whole base; its square is central, belongs to the omega four, and is
unchanged by replacing the frame over the same base. In contrast, a lift of
the basis swap admits an involutory correction when the base has order sixteen.
The latter proof uses the sixteen independent basis words and the diagonal
form of the swap square.

Multiplying either outer lift by a base element preserves the action frame
and generation. Normalizing the swap square also preserves previously proved
inversion relations. Once the inversion relations are known, only commutation
with the swap and its action on the first inner generator remain to be checked.

These are algebraic reductions for Janko–Thompson, Math. Z. 113 (1970),
1.4(c), printed p.386. They do not assert the ambient recognition step that
selects the inversion and swap relations.
-/

open Subgroup
namespace ExoticTwoGroup.ActionFrame
variable {P : Type*} [Group P] {D W B : Subgroup P}
variable (f : ActionFrame D W B)

private theorem mem_base_of_conj_eq
    (hDC : centralizer (D : Set P) ≤ D) (x : P)
    (ha : x * f.a * x⁻¹ = f.a) (hb : x * f.b * x⁻¹ = f.b) : x ∈ D := by
  apply hDC
  rw [f.base, centralizer_closure]
  intro y hy
  rcases (by simpa using hy : y = f.a ∨ y = f.b) with rfl | rfl
  · exact (mul_inv_eq_iff_eq_mul.mp ha).symm
  · exact (mul_inv_eq_iff_eq_mul.mp hb).symm

public theorem t_sq_mem_base (hDC : centralizer (D : Set P) ≤ D) : f.t ^ 2 ∈ D := by
  apply f.mem_base_of_conj_eq hDC
  · change (MulAut.conj (f.t ^ 2)) f.a = f.a
    rw [map_pow, pow_two, MulAut.mul_apply]
    change f.t * (f.t * f.a * f.t⁻¹) * f.t⁻¹ = f.a
    rw [f.t_a, f.t_b]
  · change (MulAut.conj (f.t ^ 2)) f.b = f.b
    rw [map_pow, pow_two, MulAut.mul_apply]
    change f.t * (f.t * f.b * f.t⁻¹) * f.t⁻¹ = f.b
    rw [f.t_b, f.t_a]

public theorem z_sq_mem_base (hDC : centralizer (D : Set P) ≤ D) : f.z₀ ^ 2 ∈ D := by
  apply f.mem_base_of_conj_eq hDC
  · change (MulAut.conj (f.z₀ ^ 2)) f.a = f.a
    rw [map_pow, pow_two, MulAut.mul_apply]
    change (MulAut.conj f.z₀) (f.z₀ * f.a * f.z₀⁻¹) = f.a
    rw [f.z₀_a, map_inv]
    change (f.z₀ * f.a * f.z₀⁻¹)⁻¹ = f.a
    rw [f.z₀_a, inv_inv]
  · change (MulAut.conj (f.z₀ ^ 2)) f.b = f.b
    rw [map_pow, pow_two, MulAut.mul_apply]
    change (MulAut.conj f.z₀) (f.z₀ * f.b * f.z₀⁻¹) = f.b
    rw [f.z₀_b, map_inv]
    change (f.z₀ * f.b * f.z₀⁻¹)⁻¹ = f.b
    rw [f.z₀_b, inv_inv]

public theorem z_inverts_base [IsMulCommutative D] {d : P} (hd : d ∈ D) :
    f.z₀ * d * f.z₀⁻¹ = d⁻¹ := by
  rw [f.base] at hd
  induction hd using Subgroup.closure_induction with
  | mem d hd =>
    rcases (by simpa using hd : d = f.a ∨ d = f.b) with rfl | rfl
    · exact f.z₀_a
    · exact f.z₀_b
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := (D.le_centralizer (f.base ▸ hy) x (f.base ▸ hx))
    change (MulAut.conj f.z₀) (x * y) = (x * y)⁻¹
    rw [map_mul]
    change (f.z₀ * x * f.z₀⁻¹) * (f.z₀ * y * f.z₀⁻¹) = (x * y)⁻¹
    rw [ihx, ihy, hc.mul_inv]
  | inv x hx ih =>
    change (MulAut.conj f.z₀) x⁻¹ = _
    rw [map_inv]
    change (f.z₀ * x * f.z₀⁻¹)⁻¹ = _
    rw [ih]

public theorem z_correction_square [IsMulCommutative D] {d : P} (hd : d ∈ D) :
    (d * f.z₀) ^ 2 = f.z₀ ^ 2 := by
  calc
    (d * f.z₀) ^ 2 = d * (f.z₀ * d * f.z₀⁻¹) * f.z₀ ^ 2 := by simp only [pow_two]; group
    _ = f.z₀ ^ 2 := by rw [f.z_inverts_base hd, mul_inv_cancel, one_mul]

public theorem z_four [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) : f.z₀ ^ 4 = 1 := by
  have hi := f.z_inverts_base (f.z_sq_mem_base hDC)
  have heq : f.z₀ ^ 2 = (f.z₀ ^ 2)⁻¹ := by
    calc
      f.z₀ ^ 2 = f.z₀ * f.z₀ ^ 2 * f.z₀⁻¹ := by group
      _ = (f.z₀ ^ 2)⁻¹ := hi
  calc
    f.z₀ ^ 4 = f.z₀ ^ 2 * f.z₀ ^ 2 := by rw [← pow_add]
    _ = 1 := by
      calc
        f.z₀ ^ 2 * f.z₀ ^ 2 = (f.z₀ ^ 2)⁻¹ * f.z₀ ^ 2 := congrArg (fun x => x * f.z₀ ^ 2) heq
        _ = 1 := inv_mul_cancel _

private theorem mul_inv_mem_base_of_action_eq [D.Normal]
    (hDC : centralizer (D : Set P) ≤ D) (x y : P)
    (ha : x * f.a * x⁻¹ = y * f.a * y⁻¹)
    (hb : x * f.b * x⁻¹ = y * f.b * y⁻¹) : x * y⁻¹ ∈ D := by
  have hi : y⁻¹ * x ∈ D := by
    apply f.mem_base_of_conj_eq hDC
    · calc
        (y⁻¹ * x) * f.a * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * f.a * x⁻¹) * y := by group
        _ = f.a := by rw [ha]; group
    · calc
        (y⁻¹ * x) * f.b * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * f.b * x⁻¹) * y := by group
        _ = f.b := by rw [hb]; group
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right] using
    (inferInstance : D.Normal).conj_mem (y⁻¹ * x) hi y

public theorem z_commutator_mem_base [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (x : P) :
    f.z₀ * x * f.z₀⁻¹ * x⁻¹ ∈ D := by
  have ha : f.a ∈ D := f.base.ge (subset_closure (by simp))
  have hb : f.b ∈ D := f.base.ge (subset_closure (by simp))
  have he (d : P) (hd : d ∈ D) :
      (f.z₀ * x) * d * (f.z₀ * x)⁻¹ = (x * f.z₀) * d * (x * f.z₀)⁻¹ := by
    change (MulAut.conj (f.z₀ * x)) d = (MulAut.conj (x * f.z₀)) d
    simp only [map_mul, MulAut.mul_apply]
    change f.z₀ * (x * d * x⁻¹) * f.z₀⁻¹ =
      (MulAut.conj x) (f.z₀ * d * f.z₀⁻¹)
    rw [f.z_inverts_base ((inferInstance : D.Normal).conj_mem d hd x), f.z_inverts_base hd, map_inv]
    rfl
  have hh := f.mul_inv_mem_base_of_action_eq hDC (f.z₀ * x) (x * f.z₀)
    (he f.a ha) (he f.b hb)
  simpa only [mul_inv_rev, ← mul_assoc] using hh

public theorem t_g₁_defect_mem_base [D.Normal]
    (hDC : centralizer (D : Set P) ≤ D) :
    f.t * f.g₁ * f.t⁻¹ * f.g₂⁻¹ ∈ D := by
  have hh := f.mul_inv_mem_base_of_action_eq hDC (f.t * f.g₁) (f.g₂ * f.t)
  have he := hh (by
    change (MulAut.conj (f.t * f.g₁)) f.a = (MulAut.conj (f.g₂ * f.t)) f.a
    simp only [map_mul, MulAut.mul_apply]
    change (MulAut.conj f.t) (f.g₁ * f.a * f.g₁⁻¹) =
      (MulAut.conj f.g₂) (f.t * f.a * f.t⁻¹)
    rw [f.g₁_a, f.t_a, map_inv]
    change (f.t * f.a * f.t⁻¹)⁻¹ = f.g₂ * f.b * f.g₂⁻¹
    rw [f.t_a, f.g₂_b]) (by
    change (MulAut.conj (f.t * f.g₁)) f.b = (MulAut.conj (f.g₂ * f.t)) f.b
    simp only [map_mul, MulAut.mul_apply]
    change (MulAut.conj f.t) (f.g₁ * f.b * f.g₁⁻¹) =
      (MulAut.conj f.g₂) (f.t * f.b * f.t⁻¹)
    rw [f.g₁_b, f.t_b, map_mul, map_pow, map_inv]
    change (f.t * f.a * f.t⁻¹) ^ 2 * (f.t * f.b * f.t⁻¹)⁻¹ =
      f.g₂ * f.a * f.g₂⁻¹
    rw [f.t_a, f.t_b, f.g₂_a]
    exact (f.ab.inv_left.pow_right 2).eq.symm)
  simpa only [mul_inv_rev, ← mul_assoc] using he


public theorem z_sq_mem_four [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W) : f.z₀ ^ 2 ∈ W := by
  apply hDO.le
  refine ⟨⟨f.z₀ ^ 2, f.z_sq_mem_base hDC⟩, ?_, rfl⟩
  apply Subgroup.subset_closure
  change (⟨f.z₀ ^ 2, f.z_sq_mem_base hDC⟩ : D) ^ (2 ^ 1) = 1
  apply Subtype.ext
  simpa only [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul] using f.z_four hDC

public theorem t_g₂_of_t_g₁ (ht : f.t ^ 2 = 1)
    (hg : f.t * f.g₁ * f.t⁻¹ = f.g₂) :
    f.t * f.g₂ * f.t⁻¹ = f.g₁ := by
  rw [← hg]
  calc
    f.t * (f.t * f.g₁ * f.t⁻¹) * f.t⁻¹ = f.t ^ 2 * f.g₁ * (f.t ^ 2)⁻¹ := by
      simp only [pow_two]; group
    _ = f.g₁ := by rw [ht]; simp

private theorem correction_conj [D.Normal] [IsMulCommutative D]
    {c d : P} (hc : c ∈ D) (hd : d ∈ D) (x : P) :
    (c * x) * d * (c * x)⁻¹ = x * d * x⁻¹ := by
  calc
    (c * x) * d * (c * x)⁻¹ = c * (x * d * x⁻¹) * c⁻¹ := by group
    _ = x * d * x⁻¹ := by
      rw [← D.le_centralizer hc _ ((inferInstance : D.Normal).conj_mem d hd x),
        mul_inv_cancel_right]

/-- Multiplying either outer lift by a base element preserves the action
frame, including generation. -/
@[expose] public def correctOuter [D.Normal] [IsMulCommutative D]
    (c d : P) (hc : c ∈ D) (hd : d ∈ D) : ActionFrame D W B :=
  { f with
    t := c * f.t
    z₀ := d * f.z₀
    t_a := by
      rw [correction_conj hc (f.base.ge (subset_closure (by simp))), f.t_a]
    t_b := by
      rw [correction_conj hc (f.base.ge (subset_closure (by simp))), f.t_b]
    z₀_a := by
      rw [correction_conj hd (f.base.ge (subset_closure (by simp))), f.z₀_a]
    z₀_b := by
      rw [correction_conj hd (f.base.ge (subset_closure (by simp))), f.z₀_b]
    generate := by
      let K := closure ({f.a, f.b, f.g₁, f.g₂, c * f.t, d * f.z₀} : Set P)
      have hDK : D ≤ K := by
        apply f.base.le.trans
        apply (closure_le _).mpr
        intro x hx
        rcases (by simpa using hx : x = f.a ∨ x = f.b) with rfl | rfl
        · exact subset_closure (by simp)
        · exact subset_closure (by simp)
      have ht : f.t ∈ K := by
        have hh := K.mul_mem (K.inv_mem (hDK hc))
          (subset_closure (by simp : c * f.t ∈
            ({f.a, f.b, f.g₁, f.g₂, c * f.t, d * f.z₀} : Set P)))
        simpa only [inv_mul_cancel_left] using hh
      have hz : f.z₀ ∈ K := by
        have hh := K.mul_mem (K.inv_mem (hDK hd))
          (subset_closure (by simp : d * f.z₀ ∈
            ({f.a, f.b, f.g₁, f.g₂, c * f.t, d * f.z₀} : Set P)))
        simpa only [inv_mul_cancel_left] using hh
      apply top_unique
      apply f.generate.ge.trans
      apply (closure_le _).mpr
      intro x hx
      rcases (by simpa using hx : x = f.a ∨ x = f.b ∨ x = f.g₁ ∨
        x = f.g₂ ∨ x = f.t ∨ x = f.z₀) with rfl | rfl | rfl | rfl | rfl | rfl
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · exact ht
      · exact hz }

@[simp] public theorem correctOuter_a [D.Normal] [IsMulCommutative D]
    (c d : P) (hc : c ∈ D) (hd : d ∈ D) :
    (f.correctOuter c d hc hd).a = f.a := rfl

@[simp] public theorem correctOuter_b [D.Normal] [IsMulCommutative D]
    (c d : P) (hc : c ∈ D) (hd : d ∈ D) :
    (f.correctOuter c d hc hd).b = f.b := rfl

@[simp] public theorem correctOuter_g₁ [D.Normal] [IsMulCommutative D]
    (c d : P) (hc : c ∈ D) (hd : d ∈ D) :
    (f.correctOuter c d hc hd).g₁ = f.g₁ := rfl

@[simp] public theorem correctOuter_g₂ [D.Normal] [IsMulCommutative D]
    (c d : P) (hc : c ∈ D) (hd : d ∈ D) :
    (f.correctOuter c d hc hd).g₂ = f.g₂ := rfl

@[simp] public theorem correctOuter_t [D.Normal] [IsMulCommutative D]
    (c d : P) (hc : c ∈ D) (hd : d ∈ D) :
    (f.correctOuter c d hc hd).t = c * f.t := rfl

@[simp] public theorem correctOuter_z₀ [D.Normal] [IsMulCommutative D]
    (c d : P) (hc : c ∈ D) (hd : d ∈ D) :
    (f.correctOuter c d hc hd).z₀ = d * f.z₀ := rfl

open scoped IsMulCommutative

private def coordinateMap (ij : Fin 4 × Fin 4) : D :=
  ⟨f.a ^ ij.1.val * f.b ^ ij.2.val,
    D.mul_mem (D.pow_mem (f.base.ge (subset_closure (by simp))) _)
      (D.pow_mem (f.base.ge (subset_closure (by simp))) _)⟩

private theorem coordinateMap_surjective [IsMulCommutative D] :
    Function.Surjective f.coordinateMap := by
  let a : D := ⟨f.a, f.base.ge (subset_closure (by simp))⟩
  let b : D := ⟨f.b, f.base.ge (subset_closure (by simp))⟩
  have hgen : closure ({a, b} : Set D) = ⊤ := by
    apply map_injective D.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, D.range_subtype]
    simpa only [Set.image_insert_eq, Set.image_singleton, a, b, Subgroup.coe_mk,
      Subgroup.subtype_apply] using f.base.symm
  intro d
  obtain ⟨m, n, hmn⟩ := mem_closure_pair.mp (hgen.ge (mem_top d))
  have hm0 : 0 ≤ m % 4 := Int.emod_nonneg _ (by decide)
  have hn0 : 0 ≤ n % 4 := Int.emod_nonneg _ (by decide)
  have hm4 : m % 4 < 4 := Int.emod_lt_of_pos _ (by decide)
  have hn4 : n % 4 < 4 := Int.emod_lt_of_pos _ (by decide)
  refine ⟨(⟨(m % 4).toNat, by omega⟩, ⟨(n % 4).toNat, by omega⟩), ?_⟩
  apply Subtype.ext
  change f.a ^ (m % 4).toNat * f.b ^ (n % 4).toNat = d
  rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg hm0, Int.toNat_of_nonneg hn0]
  have hm : f.a ^ (m % 4) = f.a ^ m := by
    simpa using (zpow_eq_zpow_emod' m f.a_four).symm
  have hn : f.b ^ (n % 4) = f.b ^ n := by
    simpa using (zpow_eq_zpow_emod' n f.b_four).symm
  rw [hm, hn]
  exact congrArg Subtype.val hmn

private theorem coordinateMap_injective [IsMulCommutative D]
    (hD : Nat.card D = 16) : Function.Injective f.coordinateMap := by
  exact ((Nat.bijective_iff_surjective_and_card f.coordinateMap).mpr
    ⟨f.coordinateMap_surjective, by simpa using hD.symm⟩).injective

/-- Every base element has a word with both exponents less than four. -/
public theorem exists_base_word [IsMulCommutative D] {d : P} (hd : d ∈ D) :
    ∃ i j : Fin 4, f.a ^ i.val * f.b ^ j.val = d := by
  obtain ⟨⟨i, j⟩, hij⟩ := f.coordinateMap_surjective ⟨d, hd⟩
  exact ⟨i, j, congrArg Subtype.val hij⟩

/-- In a base of order sixteen the two exponents are independent. -/
public theorem base_word_eq_iff [IsMulCommutative D] (hD : Nat.card D = 16)
    (i j k l : Fin 4) :
    f.a ^ i.val * f.b ^ j.val = f.a ^ k.val * f.b ^ l.val ↔ i = k ∧ j = l := by
  constructor
  · intro h
    have heq : (i, j) = (k, l) := f.coordinateMap_injective hD (Subtype.ext h)
    exact Prod.mk.inj heq
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A lift of the basis swap always admits an involutory correction in the
base. This uses the independence of the C₄-square basis, not ambient fusion. -/
public theorem exists_involutory_t_correction [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (hD : Nat.card D = 16) :
    ∃ c ∈ D, (c * f.t) ^ 2 = 1 := by
  obtain ⟨⟨i,j⟩, hij⟩ := f.coordinateMap_surjective ⟨f.t ^ 2, f.t_sq_mem_base hDC⟩
  have hij' : f.a ^ i.val * f.b ^ j.val = f.t ^ 2 := congrArg Subtype.val hij
  have hswap : f.a ^ j.val * f.b ^ i.val = f.a ^ i.val * f.b ^ j.val := by
    calc
      f.a ^ j.val * f.b ^ i.val = f.b ^ i.val * f.a ^ j.val :=
        (f.ab.pow_pow _ _).eq
      _ = (MulAut.conj f.t) (f.a ^ i.val * f.b ^ j.val) := by
        rw [map_mul, map_pow, map_pow]
        change _ = (f.t * f.a * f.t⁻¹) ^ i.val * (f.t * f.b * f.t⁻¹) ^ j.val
        rw [f.t_a, f.t_b]
      _ = f.t ^ 2 := by rw [hij']; change f.t * f.t ^ 2 * f.t⁻¹ = f.t ^ 2; group
      _ = f.a ^ i.val * f.b ^ j.val := hij'.symm
  have heq : (j, i) = (i, j) :=
    f.coordinateMap_injective hD (Subtype.ext hswap)
  have hji : j = i := congrArg Prod.fst heq
  subst j
  refine ⟨(f.a ^ i.val)⁻¹,
    D.inv_mem (D.pow_mem (f.base.ge (subset_closure (by simp))) _), ?_⟩
  calc
    ((f.a ^ i.val)⁻¹ * f.t) ^ 2 =
        (f.a ^ i.val)⁻¹ * ((MulAut.conj f.t) ((f.a ^ i.val)⁻¹)) * f.t ^ 2 := by
      change _ = (f.a ^ i.val)⁻¹ * (f.t * (f.a ^ i.val)⁻¹ * f.t⁻¹) * f.t ^ 2
      simp only [pow_two]; group
    _ = (f.a ^ i.val)⁻¹ * (f.b ^ i.val)⁻¹ * (f.a ^ i.val * f.b ^ i.val) := by
      rw [map_inv, map_pow, ← hij']
      rw [show (MulAut.conj f.t) f.a = f.b from f.t_a]
    _ = 1 := by rw [← (f.ab.pow_pow i.val i.val).mul_inv, inv_mul_cancel]

public theorem z_square_independent_of_frame [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (f' : ActionFrame D W B) :
    f'.z₀ ^ 2 = f.z₀ ^ 2 := by
  have ha : f.a ∈ D := f.base.ge (subset_closure (by simp))
  have hb : f.b ∈ D := f.base.ge (subset_closure (by simp))
  have hd := f.mul_inv_mem_base_of_action_eq hDC f'.z₀ f.z₀
    ((f'.z_inverts_base ha).trans f.z₀_a.symm)
    ((f'.z_inverts_base hb).trans f.z₀_b.symm)
  simpa only [inv_mul_cancel_right] using f.z_correction_square hd

public theorem z_sq_mem_center [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) : f.z₀ ^ 2 ∈ center P := by
  rw [mem_center_iff]
  intro x
  have hd : x * f.z₀ * x⁻¹ * f.z₀⁻¹ ∈ D := by
    have hh := D.inv_mem (f.z_commutator_mem_base hDC x)
    simpa only [mul_inv_rev, inv_inv, ← mul_assoc] using hh
  have hh := f.z_correction_square hd
  simp only [inv_mul_cancel_right] at hh
  have hc : x * f.z₀ ^ 2 * x⁻¹ = f.z₀ ^ 2 := by
    rw [show x * f.z₀ ^ 2 * x⁻¹ = (x * f.z₀ * x⁻¹) ^ 2 from
      (map_pow (MulAut.conj x) f.z₀ 2)]
    exact hh
  exact (mul_inv_eq_iff_eq_mul.mp hc)


/-- The inversion lift is normalized on the inner extension; the swap lift
is not constrained. -/
public structure InversionRelations : Prop where
  z₀_two : f.z₀ ^ 2 = 1
  z₀_g₁ : f.z₀ * f.g₁ * f.z₀⁻¹ = f.a * f.g₁
  z₀_g₂ : f.z₀ * f.g₂ * f.z₀⁻¹ = f.b * f.g₂

/-- Correcting the swap square preserves all inversion-lift relations. -/
public theorem exists_involutory_t_frame [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (hD : Nat.card D = 16)
    (hz : f.InversionRelations) :
    ∃ f' : ActionFrame D W B, f'.InversionRelations ∧ f'.t ^ 2 = 1 := by
  obtain ⟨c, hc, ht⟩ := f.exists_involutory_t_correction hDC hD
  refine ⟨f.correctOuter c 1 hc D.one_mem, ⟨?_, ?_, ?_⟩, ht⟩
  · change (1 * f.z₀) ^ 2 = 1
    simpa only [one_mul] using hz.z₀_two
  · change (1 * f.z₀) * f.g₁ * (1 * f.z₀)⁻¹ = f.a * f.g₁
    simpa only [one_mul] using hz.z₀_g₁
  · change (1 * f.z₀) * f.g₂ * (1 * f.z₀)⁻¹ = f.b * f.g₂
    simpa only [one_mul] using hz.z₀_g₂

/-- Only the first inner generator needs a separate swap relation. -/
public theorem liftRelations_of_inversion_and_swap (hz : f.InversionRelations)
    (ht : f.t ^ 2 = 1) (htz : Commute f.t f.z₀)
    (htg : f.t * f.g₁ * f.t⁻¹ = f.g₂) : f.LiftRelations :=
  ⟨ht, hz.z₀_two, htz, hz.z₀_g₁, hz.z₀_g₂, htg, f.t_g₂_of_t_g₁ ht htg⟩

end ExoticTwoGroup.ActionFrame
