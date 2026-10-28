module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Intrinsic block obstructions for the Lie-type refinement

The χ₀ types in C.1.12 specify both the quotient by O₂ and its actual
conjugation module. Counting those concrete models gives a necessary pair
of orders, and excludes quotient orders 168 and 20160. Consequently the
natural SL₃(2) and SL₄(2) blocks cannot be χ₀ blocks.

These calculations feed the two-parabolic argument of Aschbacher–Smith
2.3.9(7), combined manuscript of 1 March 2004, printed p.526. The binary
component calculation must still identify every possible escaping subnormal
block inside its local overgroup. `blockObstruction_of_binary_natural`
expresses that remaining input with relative subnormality intact.

The private determinant-kernel count follows the existing proof in
`Theory.SpecificGroups.PSL3Two.Cardinality`, applied in degree four. Keeping
the determinant-kernel argument in arbitrary degree avoids reducing the
finite type of all four-by-four binary matrices during kernel checking.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType
open Subgroup ChapterC
variable {K : Type*} [Group K]

/-- The three allowed types determine the orders of both the acting quotient
and its actual conjugation module. The two A₅ actions have the same orders;
this necessary condition does not identify their representations. -/
theorem chiZero_order_module (h : IsChiZeroBlock K) :
    (∃ n : ℕ, 1 < n ∧
      Nat.card (K ⧸ pCore 2 K) = 2 ^ n * (2 ^ (2 * n) - 1) ∧
      Nat.card (BlockModule K) = 2 ^ (2 * n)) ∨
    (Nat.card (K ⧸ pCore 2 K) = 3 ∧ Nat.card (BlockModule K) = 4) ∨
    (Nat.card (K ⧸ pCore 2 K) = 60 ∧ Nat.card (BlockModule K) = 16) := by
  rcases h with ⟨n, hn⟩ | h | h
  · have hm := hn.module_card
    obtain ⟨hn, _, F, _, _, hF, _, hmodel⟩ := hn
    obtain ⟨e⟩ := hmodel.quotient_iso
    refine Or.inl ⟨n, hn, ?_, by simpa [Nat.mul_comm] using hm⟩
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, hF]
    simp only [← pow_mul, Nat.mul_comm n 2]
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    · simpa using h.module_card_odd (by decide)
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    · simpa using h.module_card_odd (by decide)

/-- Except for the A₃ module, the quotient order and module order satisfy
this exact identity. It is only a necessary condition on a block. -/
theorem chiZero_quotient_square (h : IsChiZeroBlock K)
    (hm : Nat.card (BlockModule K) ≠ 4) :
    Nat.card (K ⧸ pCore 2 K) ^ 2 =
      Nat.card (BlockModule K) * (Nat.card (BlockModule K) - 1) ^ 2 := by
  rcases chiZero_order_module h with ⟨n, _, hq, hv⟩ | ⟨_, hv⟩ | ⟨hq, hv⟩
  · rw [hq, hv, mul_pow, ← pow_mul, Nat.mul_comm n 2]
  · exact (hm hv).elim
  · norm_num [hq, hv]

/-- The two-dimensional binary module can occur only for the A₃ quotient. -/
theorem chiZero_quotient_card_of_module_four (h : IsChiZeroBlock K)
    (hm : Nat.card (BlockModule K) = 4) : Nat.card (K ⧸ pCore 2 K) = 3 := by
  rcases chiZero_order_module h with ⟨n, hn, _, hv⟩ | ⟨hq, _⟩ | ⟨_, hv⟩
  · have hp : 2 ^ (2 * n) = 2 ^ 2 := hv.symm.trans hm
    have := Nat.pow_right_injective (by decide : 2 ≤ 2) hp
    omega
  · exact hq
  · omega

/-- A four-dimensional binary module forces quotient order sixty. -/
theorem chiZero_quotient_card_of_module_sixteen (h : IsChiZeroBlock K)
    (hm : Nat.card (BlockModule K) = 16) : Nat.card (K ⧸ pCore 2 K) = 60 := by
  rcases chiZero_order_module h with ⟨n, _, hq, hv⟩ | ⟨_, hv⟩ | ⟨hq, _⟩
  · have hp : 2 ^ (2 * n) = 2 ^ 4 := hv.symm.trans hm
    have := Nat.pow_right_injective (by decide : 2 ≤ 2) hp
    have hn : n = 2 := by omega
    norm_num [hn] at hq
    exact hq
  · omega
  · exact hq

/-- No χ₀ quotient has the order of SL₃(2). -/
theorem not_chiZero_of_quotient_card_168
    (hq : Nat.card (K ⧸ pCore 2 K) = 168) : ¬ IsChiZeroBlock K := by
  intro h
  rcases chiZero_order_module h with ⟨n, hn, he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · have hn3 : n < 3 := by
      by_contra hn3
      have hl : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have hr : 2 ^ 6 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      have hp := Nat.mul_le_mul hl (Nat.sub_le_sub_right hr 1)
      rw [← he, hq] at hp
      norm_num at hp
    have hn2 : n = 2 := by omega
    norm_num [hn2, hq] at he
  · omega
  · omega

/-- No χ₀ quotient has the order of SL₄(2). -/
theorem not_chiZero_of_quotient_card_20160
    (hq : Nat.card (K ⧸ pCore 2 K) = 20160) : ¬ IsChiZeroBlock K := by
  intro h
  rcases chiZero_order_module h with ⟨n, hn, he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · have hn5 : n < 5 := by
      by_contra hn5
      have hl : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have hr : 2 ^ 10 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      have hp := Nat.mul_le_mul hl (Nat.sub_le_sub_right hr 1)
      rw [← he, hq] at hp
      norm_num at hp
    interval_cases n <;> norm_num [hq] at he
  · omega
  · omega

private def slEquivDetKer (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin n) (ZMod 2) →* (ZMod 2)ˣ).ker where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A, Matrix.SpecialLinearGroup.coeToGL_det A⟩
  invFun A := ⟨A.1.val, congrArg Units.val A.property⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Units.ext rfl)

private theorem card_sl_eq_gl_two (n : ℕ) [NeZero n] :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  have h := (Matrix.GeneralLinearGroup.det :
    Matrix.GeneralLinearGroup (Fin n) (ZMod 2) →* (ZMod 2)ˣ).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective,
    Subgroup.card_top, ← Nat.card_congr (slEquivDetKer n)] at h
  have hu : Nat.card (ZMod 2)ˣ = 1 := by rw [Nat.card_units]; norm_num
  simpa only [hu, mul_one] using h

private theorem card_sl_four_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [card_sl_eq_gl_two, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

/-- The natural three-dimensional binary module excludes a χ₀ block. -/
theorem not_chiZero_of_linearThreeTwo (h : IsLinearTwoBlock K 3) :
    ¬ IsChiZeroBlock K :=
  not_chiZero_of_odd_module_card 1 (by simpa using h.module_card)

/-- The natural four-dimensional binary block has quotient SL₄(2),
whereas a χ₀ block with that module order has quotient order sixty. -/
theorem not_chiZero_of_linearFourTwo (h : IsLinearTwoBlock K 4) :
    ¬ IsChiZeroBlock K := by
  intro hc
  have hq := chiZero_quotient_card_of_module_sixteen hc (by simpa using h.module_card)
  obtain ⟨e⟩ := h.2.2.2.quotient_iso
  rw [Nat.card_congr e.toEquiv, card_sl_four_two] at hq
  contradiction

variable {G : Type*} [Group G]

/-- Convert a calculation of every escaping relative block into the obstruction
used by `le_of_pair_blockObstruction`. The model calculation must establish the
natural types for subnormal subgroups of P; identifying P itself is insufficient. -/
theorem blockObstruction_of_binary_natural {M S P : Subgroup G}
    (hlocal : ∀ B : Subgroup P, IsBlock B →
      B.map P.subtype = ⁅B.map P.subtype, Stellmacher.elementaryAbelianMaxJ S⁆ →
      ¬ B.map P.subtype ≤ M → IsLinearTwoBlock B 3 ∨ IsLinearTwoBlock B 4) :
    BlockObstruction M S P := by
  intro B hb hm
  by_contra hout
  rcases hlocal B hb.1 hm hout with h3 | h4
  · exact not_chiZero_of_linearThreeTwo h3 hb.2
  · exact not_chiZero_of_linearFourTwo h4 hb.2

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType

end
