module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeSylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# No copy of C₄ × C₄ in A₉

Extend the binary-tree subgroup of S₈ by fixing the ninth point. Its order is
128, the full two-part of 9!, so every two-subgroup of S₉ can be conjugated
into it. In this tree group, commuting even permutations with nontrivial
squares have the same square. A kernel-checked calculation on its 128 normal
forms proves this assertion, discarding odd permutations and square-one
permutations before checking pairs. The two standard generators of C₄ × C₄
have distinct nontrivial squares, which excludes an injective map into A₉.

Application: the index-nine case for the actual G₂(2)′ model in the proof of
Aschbacher–Smith, B.1.13, printed p.74 / PDF p.85 of `refs/quasithin.pdf`.
The existing `Atlas.G2.BinaryNinePointReduction` consumes exactly this
nonembedding statement; its group-specific assembly remains separate.
-/

public section

open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open scoped Pointwise

namespace Theory.SpecificGroups.Alternating.NineCyclicFourSquare
private abbrev S9 := Equiv.Perm (Fin 9)
private abbrev C4Square := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

private def firstEight : Fin 8 ≃ {x : Fin 9 // x.val < 8} where
  toFun x := ⟨⟨x.val, Nat.lt_trans x.isLt (by decide)⟩, x.isLt⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def extend : S8 →* S9 := Equiv.Perm.extendDomainHom firstEight

private theorem extend_injective : Function.Injective extend :=
  Equiv.Perm.extendDomainHom_injective firstEight

private theorem sign_extend (x : S8) : (extend x).sign = x.sign :=
  Equiv.Perm.sign_extendDomain x firstEight

private noncomputable def nineSylow : Sylow 2 S9 :=
  Sylow.ofCard (treeGroup.map extend) (by
    rw [← Nat.card_congr (treeGroup.equivMapOfInjective extend extend_injective).toEquiv,
      card_treeGroup]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [show 362880 = 2 ^ 7 * 2835 by rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 2835)])

-- Prune each row before enumerating its potential commuting partners.
set_option maxRecDepth 10000 in
private theorem even_tree_nontrivial_sq_eq : ∀ i : Fin 128,
    ((treeWord i).sign = 1 ∧ treeWord i ^ 2 ≠ 1) → ∀ j : Fin 128,
    ((treeWord j).sign = 1 ∧ treeWord j ^ 2 ≠ 1) →
    treeWord i * treeWord j = treeWord j * treeWord i →
    treeWord i ^ 2 = treeWord j ^ 2 := by
  decide +kernel

private theorem mapped_square
    (x y : S9) (hx : x ∈ (nineSylow : Subgroup S9))
    (hy : y ∈ (nineSylow : Subgroup S9))
    (hex : x.sign = 1) (hey : y.sign = 1) (hc : x * y = y * x) :
    x ^ 2 = 1 ∨ y ^ 2 = 1 ∨ x ^ 2 = y ^ 2 := by
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  obtain ⟨i, rfl⟩ := (mem_treeGroup x).mp hx
  obtain ⟨j, rfl⟩ := (mem_treeGroup y).mp hy
  have hexi := (sign_extend (treeWord i)).symm.trans hex
  have heyj := (sign_extend (treeWord j)).symm.trans hey
  have hcij : treeWord i * treeWord j = treeWord j * treeWord i :=
    extend_injective (by simpa only [map_mul] using hc)
  have hs : treeWord i ^ 2 = 1 ∨ treeWord j ^ 2 = 1 ∨
      treeWord i ^ 2 = treeWord j ^ 2 := by
    by_cases hi : treeWord i ^ 2 = 1
    · exact Or.inl hi
    by_cases hj : treeWord j ^ 2 = 1
    · exact Or.inr (Or.inl hj)
    exact Or.inr (Or.inr
      (even_tree_nontrivial_sq_eq i ⟨hexi, hi⟩ j ⟨heyj, hj⟩ hcij))
  rcases hs with h | h | h
  · left; simpa only [map_pow, map_one] using congrArg extend h
  · right; left; simpa only [map_pow, map_one] using congrArg extend h
  · right; right; simpa only [map_pow] using congrArg extend h

/-- The alternating group on nine letters contains no subgroup isomorphic to
C₄ × C₄, with the cyclic factors given by the literal multiplicative ZMod model. -/
theorem not_injective
    (f : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →*
      alternatingGroup (Fin 9)) : ¬ Function.Injective f := by
  classical
  intro hf
  let g : C4Square →* S9 := (alternatingGroup (Fin 9)).subtype.comp f
  have hg : Function.Injective g := Subtype.val_injective.comp hf
  have hp : IsPGroup 2 C4Square := IsPGroup.of_card (n := 4) (by
    norm_num [Nat.card_eq_fintype_card, C4Square])
  obtain ⟨P, hP⟩ := (hp.of_surjective g.rangeRestrict g.rangeRestrict_surjective).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq S9 P nineSylow
  let h : C4Square →* S9 := (MulAut.conj c).toMonoidHom.comp g
  have hh : Function.Injective h := (MulAut.conj c).injective.comp hg
  have hmem (a : C4Square) : h a ∈ (nineSylow : Subgroup S9) := by
    rw [← hc]
    change (MulAut.conj c) • g a ∈ (MulAut.conj c) • (P : Subgroup S9)
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hP ⟨a, rfl⟩)
  have heven (a : C4Square) : (h a).sign = 1 := by
    have ha : (g a).sign = 1 := Equiv.Perm.mem_alternatingGroup.mp (f a).property
    simp [h, MulAut.conj_apply, ha]
  let a : C4Square := (Multiplicative.ofAdd 1, 1)
  let b : C4Square := (1, Multiplicative.ofAdd 1)
  have hab : h a * h b = h b * h a := by rw [← map_mul, ← map_mul, mul_comm a b]
  rcases mapped_square (h a) (h b) (hmem a) (hmem b) (heven a) (heven b) hab with
    ha | hb | hab
  · have ha' : a ^ 2 = 1 := hh (by simpa only [map_pow, map_one] using ha)
    exact (by decide : a ^ 2 ≠ 1) ha'
  · have hb' : b ^ 2 = 1 := hh (by simpa only [map_pow, map_one] using hb)
    exact (by decide : b ^ 2 ≠ 1) hb'
  · have hab' : a ^ 2 = b ^ 2 := hh (by simpa only [map_pow] using hab)
    exact (by decide : a ^ 2 ≠ b ^ 2) hab'
end Theory.SpecificGroups.Alternating.NineCyclicFourSquare
