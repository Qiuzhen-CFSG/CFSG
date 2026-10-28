module

public import Theory.Mathieu.M23.Properties.TwoRank
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.GroupTheory.PrimeRankHom

/-!
# Intrinsic two-rank bounds for M₂₂ and its automorphism group

The native point-stabilizer equivalence embeds M₂₂ in M₂₃, giving rank at
most four. The full hexad-design automorphism group contains M₂₂ with
index two. Its proved identification with the abstract automorphism group
therefore gives the upper bound five.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.3,
printed p.348. These are group-theoretic bounds, independent of any module.
-/

public section
namespace Sporadic.Mathieu
open Theory.GroupTheory

/-- The intrinsic two-rank bound for the native simple M₂₂. -/
theorem m22_twoRank_le_four : primeRank 2 M22 ≤ 4 := by
  let f : M22 →* M23 := (MulAction.stabilizer M23 (9 : Fin 23)).subtype.comp
    m23EquivM22PointStabilizer.toMonoidHom
  exact (primeRank_le_of_injective 2 f
    (Subtype.val_injective.comp m23EquivM22PointStabilizer.injective)).trans
      m23_twoRank_le_four

/-- The full abstract automorphism group of M₂₂ has two-rank at most five. -/
theorem m22_automorphism_twoRank_le_five : primeRank 2 (MulAut M22) ≤ 5 := by
  let e : m22DesignAut ≃* MulAut M22 := MulEquiv.ofBijective m22DesignAutToAut
    ⟨m22DesignAutToAut_injective, m22DesignAutToAut_surjective⟩
  rw [← primeRank_equiv 2 e]
  let C := M22.subgroupOf m22DesignAut
  have hC : C.index ≤ 2 ^ 1 := by
    have he : C = m22EvenDesignAut := by
      ext g
      simp [C, M22, m22EvenDesignAut]
    rw [he, m22EvenDesignAut_index]
    decide
  have hr := primeRank_le_add_of_index_le C hC
  have he : C ≃* M22 := Subgroup.subgroupOfEquivOfLe M22_le_hexadDesignAut
  rw [primeRank_equiv 2 he] at hr
  exact hr.trans (Nat.add_le_add_right m22_twoRank_le_four 1)

end Sporadic.Mathieu
