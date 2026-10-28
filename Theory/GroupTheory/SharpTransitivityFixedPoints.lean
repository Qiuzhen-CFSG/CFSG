module

public import Theory.GroupTheory.SharpTransitivity
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Sharp transitivity from fixed-point bounds

If nonidentity elements fix fewer than `n` points, the action on ordered
`n`-tuples of distinct points is free. When the group order equals the number
of such tuples, every orbit map is bijective, giving sharp transitivity.
This is the final counting argument in Wong (1964), Theorem 6(a), p.108,
DOI 10.1017/S1446788700022771.
-/

namespace Theory.GroupTheory.MulAction

variable {G α : Type*} [Group G] [MulAction G α] [Fintype α]

/-- A bound on fixed points makes the orbit map on distinct tuples injective. -/
public theorem injective_tuple_orbitMap_of_fixedBy_lt {n : ℕ}
    (hfix : ∀ g : G, g ≠ 1 → Nat.card (_root_.MulAction.fixedBy α g) < n)
    (x : Fin n ↪ α) : Function.Injective (fun g : G => g • x) := by
  intro a b hab
  have hfixed (i : Fin n) : (b⁻¹ * a) • x i = x i := by
    have hi : a • x i = b • x i := congrArg (fun e : Fin n ↪ α => e i) hab
    rw [mul_smul, hi, inv_smul_smul]
  have hid : b⁻¹ * a = 1 := by
    by_contra hne
    let e : Fin n ↪ _root_.MulAction.fixedBy α (b⁻¹ * a) :=
      ⟨fun i => ⟨x i, hfixed i⟩, fun i j hij => x.injective (congrArg Subtype.val hij)⟩
    have hle := Nat.card_le_card_of_injective e e.injective
    rw [Nat.card_fin] at hle
    exact (not_lt_of_ge hle) (hfix _ hne)
  exact (inv_mul_eq_one.mp hid).symm

/-- A free action on distinct tuples with the right order is sharply transitive. -/
public theorem isSharplyMultiplyPretransitive_of_fixedBy_lt {n : ℕ}
    (base : Fin n ↪ α)
    (hfix : ∀ g : G, g ≠ 1 → Nat.card (_root_.MulAction.fixedBy α g) < n)
    (hcard : Nat.card G = (Fintype.card α).descFactorial n) :
    IsSharplyMultiplyPretransitive G α n := by
  apply isSharplyMultiplyPretransitive_of_bijective_orbitMap base
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨injective_tuple_orbitMap_of_fixedBy_lt hfix base, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
    Fintype.card_fin] using hcard

/-- The fixed-point bound also gives faithfulness when at least `n` points exist. -/
public theorem faithfulSMul_of_fixedBy_lt {n : ℕ} (hn : n ≤ Fintype.card α)
    (hfix : ∀ g : G, g ≠ 1 → Nat.card (_root_.MulAction.fixedBy α g) < n) :
    FaithfulSMul G α := by
  constructor
  intro a b hab
  have hid : b⁻¹ * a = 1 := by
    by_contra hne
    have hfixed (x : α) : (b⁻¹ * a) • x = x := by
      rw [mul_smul, hab x, inv_smul_smul]
    let e : α ↪ _root_.MulAction.fixedBy α (b⁻¹ * a) :=
      ⟨fun x => ⟨x, hfixed x⟩, fun _ _ h => congrArg Subtype.val h⟩
    have hle := Nat.card_le_card_of_injective e e.injective
    rw [Nat.card_eq_fintype_card] at hle
    exact (not_lt_of_ge (hn.trans hle)) (hfix _ hne)
  exact (inv_mul_eq_one.mp hid).symm

end Theory.GroupTheory.MulAction
