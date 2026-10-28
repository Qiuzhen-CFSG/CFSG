module

public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation.Planes

/-!
# Orienting the six roots over a binary field

An automorphism preserving the specified opposite unipotent pair permutes
both pairs of maximal elementary abelian planes. Intersecting the upper
group with a lower-plane normalizer recovers each positive simple root;
the reversed construction recovers the negative simple roots. Containment
in the upper planes forces the two permutations to agree. The intersections
of the two planes recover the highest roots. The resulting permutation is
the identity or coordinate reversal, corrected by the actual opposition
graph automorphism.

This proves the root-orientation input to the binary standard-coverage
assembly, including q = 4. The argument uses no simplicity hypothesis and
in fact works over every finite field of characteristic two.
Source: the normalization step toward GLS3 Theorem 2.5.12(a) and the matrix
conventions in §2.7, `refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115.
-/

public section

open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.RootPlaneGeometry
namespace Matrix.PSL3Even.AutomorphismCoverage
open RootOrientation
variable (F : Type*) [Field F] [Finite F]

/-- In characteristic two, opposite-plane normalizers and plane containment
force the same diagram orientation on positive and negative roots. -/
theorem exists_oppositionGraph_preserves_roots_of_charTwo [CharP F 2]
    (α : MulAut PSL(3,F)) (hα : PreservesUnipotentPair F α) :
    ∃ ε : Fin 2, PreservesRootGroups ((oppositionGraph F ^ (ε : ℕ))⁻¹ * α) := by
  obtain ⟨b,hb₁,hb₂⟩ := upper_plane_permutation F α hα.1
  obtain ⟨c,hc₁,hc₂⟩ := lower_plane_permutation F α hα.2
  have hp (i j : Bool) (h : (lowerPlane F i).map α.toMonoidHom = lowerPlane F j) :
      (positiveRoot (F:=F) (simpleIndex i)).map α.toMonoidHom = positiveRoot (simpleIndex j) := by
    rw [← upper_inf_normalizer_lowerPlane F i,
      Subgroup.map_inf _ _ α.toMonoidHom α.injective, Subgroup.map_equiv_normalizer_eq,
      hα.1, h, upper_inf_normalizer_lowerPlane]
  have hn (i j : Bool) (h : (rootPlane F i).map α.toMonoidHom = rootPlane F j) :
      (negativeRoot (F:=F) (simpleIndex i)).map α.toMonoidHom = negativeRoot (simpleIndex j) := by
    rw [← lower_inf_normalizer_rootPlane F i,
      Subgroup.map_inf _ _ α.toMonoidHom α.injective, Subgroup.map_equiv_normalizer_eq,
      hα.2, h, lower_inf_normalizer_rootPlane]
  have hcb : c = b := by
    apply (simpleRoot_plane_iff F c b).mp
    have h := Subgroup.map_mono (f:=α.toMonoidHom) (simpleRoot_le_plane F true)
    change (positiveRoot (simpleIndex true)).map α.toMonoidHom ≤
      (rootPlane F false).map α.toMonoidHom at h
    rw [hp true c hc₁, hb₂] at h
    exact h
  subst c
  have hp₀ := hp true b hc₁
  have hp₂ := hp false (!b) hc₂
  have hn₀ := hn true b hb₁
  have hn₂ := hn false (!b) hb₂
  have hp₁ : (positiveRoot (F:=F) 1).map α.toMonoidHom = positiveRoot 1 := by
    rw [← planes_inter, Subgroup.map_inf _ _ α.toMonoidHom α.injective, hb₁, hb₂]
    cases b
    · exact inf_comm _ _
    · rfl
  have hn₁ : (negativeRoot (F:=F) 1).map α.toMonoidHom = negativeRoot 1 := by
    rw [← lowerPlanes_inter, Subgroup.map_inf _ _ α.toMonoidHom α.injective, hc₁, hc₂]
    cases b
    · exact inf_comm _ _
    · rfl
  cases b
  · apply exists_oppositionGraph_of_root_permutation α
      (Function.Involutive.toPerm Fin.rev Fin.rev_rev) (by rfl)
    · intro k
      fin_cases k
      · exact hp₀
      · exact hp₁
      · exact hp₂
    · intro k
      fin_cases k
      · exact hn₀
      · exact hn₁
      · exact hn₂
  · apply exists_oppositionGraph_of_root_permutation α (Equiv.refl _) (by rfl)
    · intro k
      fin_cases k
      · exact hp₀
      · exact hp₁
      · exact hp₂
    · intro k
      fin_cases k
      · exact hn₀
      · exact hn₁
      · exact hn₂

/-- The binary opposite-pair root-orientation input to standard coverage,
including the four-element field. -/
theorem exists_oppositionGraph_preserves_roots {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) (α : MulAut PSL(3,F))
    (hα : PreservesUnipotentPair F α) :
    ∃ ε : Fin 2, PreservesRootGroups ((oppositionGraph F ^ (ε : ℕ))⁻¹ * α) := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, show n ≠ 0 by omega])
  let : CharP F 2 := ringChar.of_eq hc
  exact exists_oppositionGraph_preserves_roots_of_charTwo F α hα
end Matrix.PSL3Even.AutomorphismCoverage
