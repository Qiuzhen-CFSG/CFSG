module

public import Theory.GroupTheory.SubgroupEnumeration
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Normal forms for the finite cyclic extensions in the J₃ certificate

If a new generator normalizes the preceding subgroup and its p-th power lies
there, adjoining it gives at most p cosets. Iteration gives mixed-radix normal
forms. All hypotheses are actual group identities, supplied by the permutation
certificates; no presentation or external computation is trusted.
-/

open Subgroup
open scoped Pointwise
namespace Sporadic.Janko3.TwoLocal.ThompsonCertificate.NormalForm
variable {G : Type*} [Group G]
@[expose] public def series (g : ℕ → G) : ℕ → Subgroup G
  | 0 => ⊥
  | n+1 => zpowers (g n) ⊔ series g n

public theorem series_le_iff (g : ℕ → G) (n : ℕ) (H : Subgroup G) :
    series g n ≤ H ↔ ∀ i < n, g i ∈ H := by
  induction n with
  | zero => simp [series]
  | succ n ih =>
    rw [series, sup_le_iff, zpowers_le, ih]
    constructor
    · rintro ⟨hn, h⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

public theorem gen_mem (g : ℕ → G) {i n : ℕ} (h : i < n) : g i ∈ series g n :=
  (series_le_iff g n _).mp le_rfl i h

public theorem series_mono (g : ℕ → G) {m n : ℕ} (h : m ≤ n) : series g m ≤ series g n :=
  (series_le_iff g m _).mpr (fun i hi => gen_mem g (by omega))

public theorem normalizes (g : ℕ → G) (n : ℕ) (x : G)
    (hf : ∀ i < n, x * g i * x⁻¹ ∈ series g n)
    (hb : ∀ i < n, x⁻¹ * g i * x ∈ series g n) :
    x ∈ normalizer (series g n : Set G) := by
  have f : series g n ≤ (series g n).comap (MulAut.conj x).toMonoidHom :=
    (series_le_iff g n _).mpr hf
  have b : series g n ≤ (series g n).comap (MulAut.conj x⁻¹).toMonoidHom :=
    (series_le_iff g n _).mpr (by simpa only [mem_comap, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv] using hb)
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => f hy
  · intro hy
    have := b hy
    simpa only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using this

public theorem extension_cover [Finite G] (H : Subgroup G) (g : G) (p : ℕ)
    (hp : 0 < p) (hn : g ∈ normalizer (H : Set G)) (hg : g ^ p ∈ H)
    {x : G} (hx : x ∈ zpowers g ⊔ H) :
    ∃ i : Fin p, ∃ y : H, x = g ^ i.val * (y : G) := by
  have hx' : x ∈ (zpowers g : Set G) * (H : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ (zpowers_le.mpr hn)]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  change a ∈ zpowers g at ha
  rw [← mem_powers_iff_mem_zpowers] at ha
  obtain ⟨j, rfl⟩ := ha
  refine ⟨⟨j % p, Nat.mod_lt _ hp⟩,
    ⟨(g ^ p) ^ (j / p) * b, H.mul_mem (H.pow_mem hg _) hb⟩, ?_⟩
  change g ^ j * b = g ^ (j % p) * ((g ^ p) ^ (j / p) * b)
  rw [← mul_assoc, ← pow_mul, ← pow_add, Nat.mod_add_div]

@[expose] public def size (p : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => p n * size p n

@[expose] public def rep (g : ℕ → G) (p : ℕ → ℕ) : ℕ → ℕ → G
  | 0, _ => 1
  | n+1, r => g n ^ (r / size p n) * rep g p n (r % size p n)

public theorem rep_mem (g : ℕ → G) (p : ℕ → ℕ) (n r : ℕ) :
    rep g p n r ∈ series g n := by
  induction n generalizing r with
  | zero => exact (series g 0).one_mem
  | succ n ih =>
    exact (series g (n+1)).mul_mem
      (mem_sup_left (npow_mem_zpowers _ _)) (mem_sup_right (ih _))

public theorem cover [Finite G] (g : ℕ → G) (p : ℕ → ℕ) (n : ℕ)
    (hp : ∀ i < n, 0 < p i)
    (hn : ∀ i < n, g i ∈ normalizer (series g i : Set G))
    (hg : ∀ i < n, g i ^ p i ∈ series g i) :
    ∀ x ∈ series g n, ∃ r : Fin (size p n), x = rep g p n r.val := by
  induction n with
  | zero =>
    intro x hx
    exact ⟨⟨0, Nat.zero_lt_one⟩, (mem_bot.mp hx)⟩
  | succ n ih =>
    have hp' : ∀ i < n, 0 < p i := fun i hi => hp i (by omega)
    have hs : 0 < size p n := by
      suffices ∀ m, (∀ i < m, 0 < p i) → 0 < size p m from this n hp'
      intro m hm
      induction m with
      | zero => exact Nat.zero_lt_one
      | succ m ih =>
        exact Nat.mul_pos (hm m (by omega)) (ih (fun i hi => hm i (by omega)))
    intro x hx
    obtain ⟨i, y, hy⟩ := extension_cover (series g n) (g n) (p n)
      (hp n (by omega)) (hn n (by omega)) (hg n (by omega)) hx
    obtain ⟨r, hr⟩ := ih hp' (fun i hi => hn i (by omega))
      (fun i hi => hg i (by omega)) y y.property
    refine ⟨⟨r.val + size p n * i.val, ?_⟩, ?_⟩
    · change _ < p n * size p n
      calc
        r.val + size p n * i.val < size p n + size p n * i.val :=
          Nat.add_lt_add_right r.isLt _
        _ = size p n * (i.val + 1) := by simp [Nat.mul_add, Nat.add_comm]
        _ ≤ size p n * p n := Nat.mul_le_mul_left _ (by omega)
        _ = p n * size p n := Nat.mul_comm _ _
    · simpa only [rep, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt r.isLt,
        Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt, ← hr] using hy
end Sporadic.Janko3.TwoLocal.ThompsonCertificate.NormalForm
