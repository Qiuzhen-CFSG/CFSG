module

public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Counting a normalizer from a transitive class intersection

If N_G(A) is transitive on the ambient conjugates of z in A, its order is
the size of that class intersection times the order of N_G(A)∩C_G(z).
The proof uses the literal conjugation action and identifies its stabilizer.

Source application: Aschbacher--Smith F.5.4(4), printed p.301.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem card_normalizer_of_class_transitive (A : Subgroup G) (z : G) (hz : z ∈ A)
    (ht : ∀ y ∈ A, IsConj z y →
      ∃ n ∈ normalizer (A : Set G), MulAut.conj n z = y) :
    Nat.card {a : A // IsConj z a.val} *
      Nat.card (normalizer (A : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) =
      Nat.card (normalizer (A : Set G)) := by
  let N := normalizer (A : Set G)
  let := conjMulDistribMulActionOfLeNormalizer N A le_rfl
  let a : A := ⟨z,hz⟩
  have horbit : MulAction.orbit N a = {b : A | IsConj z b.val} := by
    ext b
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n,rfl⟩
      exact isConj_iff.mpr ⟨n.val,rfl⟩
    · intro hb
      obtain ⟨n,hn,he⟩ := ht b.val b.property hb
      exact ⟨⟨n,hn⟩,Subtype.ext he⟩
  have hstab : MulAction.stabilizer N a =
      (N ⊓ centralizer ({z} : Set G)).subgroupOf N := by
    ext n
    change n • a = a ↔ n.val ∈ N ⊓ centralizer ({z} : Set G)
    constructor
    · intro he
      refine ⟨n.property,mem_centralizer_singleton_iff.mpr ?_⟩
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
    · intro he
      apply Subtype.ext
      change n.val * z * n.val⁻¹ = z
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp he.2)
  have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N a)
  rw [Nat.card_prod,horbit,hstab,
    Nat.card_congr (subgroupOfEquivOfLe (show N ⊓ centralizer ({z} : Set G) ≤ N from inf_le_left)).toEquiv] at hh
  exact hh

end Subgroup
