module

public import Theory.GroupTheory.PGroup.OmegaImage
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Index

/-!
# Restricting elementary actions to omega subgroups

In an abelian group, omega is a power-map kernel. Consequently the `k`th
binary omega subgroup of `C_(2^n) × C_(2^m)` is `C_(2^k) × C_(2^k)` whenever
`k ≤ n, m`. Restriction to eighth roots preserves the fourth-root action image.

For an elementary binary action, choose a vector-space complement to the
kernel of restriction. Its action on the original group is faithful and its
image is faithful on fourth roots. Thus a cardinal bound for faithful actions
also bounds the restriction image of an arbitrary elementary action.

These are power-kernel and vector-space arguments supporting the abelian
subgroup reductions in MacWilliams, *On 2-groups with no normal abelian
subgroups of rank 3*, Trans. AMS 150 (1970), §1.2.
-/

open Subgroup
open scoped IsMulCommutative

namespace OmegaAction

/-- In a commutative group, omega is the kernel of the corresponding power map. -/
public theorem omega_eq_pow_ker {G : Type*} [Group G] [IsMulCommutative G] (p k : ℕ) :
    omega G (p := p) k = (powMonoidHom (p^k) : G →* G).ker := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    exact hx
  · intro x hx
    exact subset_closure hx

/-- The first `k` omega layers of a cyclic group of order `2^n` form `C_(2^k)`. -/
public noncomputable def cyclicOmegaEquiv (n k : ℕ) (hk : k ≤ n) :
    omega (Multiplicative (ZMod (2^n))) (p := 2) k ≃*
      Multiplicative (ZMod (2^k)) := by
  rw [omega_eq_pow_ker]
  apply mulEquivOfCyclicCardEq
  rw [IsCyclic.card_powMonoidHom_ker]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact Nat.gcd_eq_right (pow_dvd_pow 2 hk)

/-- Below both cyclic exponents, the omega subgroup is homocyclic. -/
public noncomputable def productOmegaEquiv (n m k : ℕ) (hkn : k ≤ n) (hkm : k ≤ m) :
    omega (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^m))) (p := 2) k ≃*
      (Multiplicative (ZMod (2^k)) × Multiplicative (ZMod (2^k))) := by
  have he : omega (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^m))) (p := 2) k =
      (omega (Multiplicative (ZMod (2^n))) (p := 2) k).prod
        (omega (Multiplicative (ZMod (2^m))) (p := 2) k) := by
    simp only [omega_eq_pow_ker]
    ext x
    change x ^ (2^k) = 1 ↔ x.1 ^ (2^k) = 1 ∧ x.2 ^ (2^k) = 1
    exact Prod.ext_iff
  exact (MulEquiv.subgroupCongr he).trans ((prodEquiv _ _).trans
    ((cyclicOmegaEquiv n k hkn).prodCongr (cyclicOmegaEquiv m k hkm)))

/-- An elementary binary action has a faithful subgroup with the same image. -/
public theorem exists_faithful_subgroup {E F : Type*} [Group E] [Group F]
    [IsElementaryAbelian 2 E] (f : E →* F) :
    ∃ B : Subgroup E, Function.Injective (f.comp B.subtype) ∧
      (f.comp B.subtype).range = f.range := by
  obtain ⟨B, hB⟩ := IsElementaryAbelian.exists_isCompl 2 E f.ker
  refine ⟨B, ?_, ?_⟩
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hx1 : (x : E) = 1 := disjoint_def.mp hB.disjoint hx x.property
    exact Subtype.ext hx1
  · rw [MonoidHom.range_comp, range_subtype]
    have h := congrArg (Subgroup.map f) hB.sup_eq_top
    simpa only [Subgroup.map_sup, Subgroup.map_ker_self, bot_sup_eq, ← MonoidHom.range_eq_map] using h

/-- Restriction of automorphisms to a characteristic omega subgroup. -/
@[expose] public noncomputable def omegaRestriction (H : Type*) [Group H] (p k : ℕ) :
    MulAut H →* MulAut (omega H (p := p) k) := by
  letI : (omega H (p := p) k).Characteristic := omega_characteristic H k
  exact MulAut.characteristic _

/-- Triviality of restriction is equivalent to fixing every relevant root of unity. -/
public theorem mem_ker_restriction_iff {E H : Type*} [Group E] [Group H]
    [IsMulCommutative H] (ρ : E →* MulAut H) (p k : ℕ) (a : E) :
    a ∈ ((omegaRestriction H p k).comp ρ).ker ↔
      ∀ x : H, x ^ (p^k) = 1 → ρ a x = x := by
  constructor
  · intro ha x hx
    have hxO : x ∈ omega H (p := p) k := subset_closure hx
    exact congrArg (fun f : MulAut (omega H (p := p) k) =>
      (f ⟨x, hxO⟩ : H)) (MonoidHom.mem_ker.mp ha)
  · intro h
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact h x (show (x : H) ∈ (powMonoidHom (p^k) : H →* H).ker from
      omega_eq_pow_ker (G := H) p k ▸ x.property)

/-- A bound for elementary actions faithful on fourth roots bounds every
elementary fourth-root action image. -/
public theorem card_restriction_range_le_of_faithful_bound
    {E H : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    [Group H] [Finite H] [IsMulCommutative H]
    (ρ : E →* MulAut H)
    (hfix : ∀ a : E, ∀ x : H, x^2=1 → ρ a x=x)
    (hbound : ∀ B : Subgroup (MulAut H), IsElementaryAbelian 2 B →
      (∀ a ∈ B, ∀ x : H, x^2=1 → a x=x) →
      (∀ a ∈ B, (∀ x : H, x^4=1 → a x=x) → a=1) → Nat.card B ≤ 4) :
    Nat.card ((omegaRestriction H 2 2).comp ρ).range ≤ 4 := by
  let r := (omegaRestriction H 2 2).comp ρ
  obtain ⟨C, hC, hCr⟩ := exists_faithful_subgroup r
  let J := C.map ρ
  let : IsElementaryAbelian 2 C := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x) }
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map ρ
  have hj : Function.Injective (ρ.comp C.subtype) := by
    intro a b h
    apply hC
    exact congrArg (omegaRestriction H 2 2) h
  have hJ : (ρ.comp C.subtype).range = J := by
    rw [MonoidHom.range_comp, range_subtype]
  have hb : Nat.card J ≤ 4 := by
    apply hbound J inferInstance
    · rintro a ⟨c, _, rfl⟩ x hx
      exact hfix c x hx
    · rintro a ⟨c, hc, rfl⟩ ha
      have hr : c ∈ r.ker := (mem_ker_restriction_iff ρ 2 2 c).mpr ha
      have hc1 : (⟨c, hc⟩ : C) = 1 := hC (by
        change r c = r 1
        rw [map_one]
        exact MonoidHom.mem_ker.mp hr)
      have hcE : c = 1 := congrArg Subtype.val hc1
      rw [hcE, map_one]
  calc
    Nat.card r.range = Nat.card (r.comp C.subtype).range := by rw [hCr]
    _ = Nat.card C := (Nat.card_congr (MonoidHom.ofInjective hC).toEquiv).symm
    _ = Nat.card J := (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).trans
      (by rw [hJ])
    _ ≤ 4 := hb

/-- Restricting an action first to eighth roots preserves its fourth-root image order. -/
public theorem card_fourth_root_range_eq_on_eighth_roots
    {E H : Type*} [Group E] [Finite E] [Group H] [IsMulCommutative H]
    (ρ : E →* MulAut H) :
    Nat.card ((omegaRestriction H 2 2).comp ρ).range =
      Nat.card ((omegaRestriction (omega H (p := 2) 3) 2 2).comp
        ((omegaRestriction H 2 3).comp ρ)).range := by
  have hk : ((omegaRestriction H 2 2).comp ρ).ker =
      ((omegaRestriction (omega H (p := 2) 3) 2 2).comp
        ((omegaRestriction H 2 3).comp ρ)).ker := by
    ext a
    rw [mem_ker_restriction_iff, mem_ker_restriction_iff]
    constructor
    · intro h x hx
      apply Subtype.ext
      exact h x (congrArg Subtype.val hx)
    · intro h x hx
      have hxO : x ∈ omega H (p := 2) 3 := subset_closure (by
        change x ^ 8 = 1
        rw [show 8 = 4 * 2 by decide, pow_mul, show x^4=1 from hx, one_pow])
      exact congrArg Subtype.val (h ⟨x, hxO⟩ (Subtype.ext hx))
  rw [← index_ker, ← index_ker, hk]

end OmegaAction
