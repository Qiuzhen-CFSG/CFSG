module
public import ABG.Recognition.ThreeMathieuCharacterData
public import Theory.Character.Permutation
public import Theory.GroupAction.TransportFixedPoints

/-!
# The eleven-coset character in Wong's order-7920 branch

For any subgroup of index eleven, the transitive permutation representation
has one principal constituent. Every nonprincipal irreducible has degree at
least ten, so the remaining constituent is one of the three degree-ten
characters in the shared catalog. Two have value `-2` at the involution;
adding the principal character would give a negative fixed-point count.
Consequently the coset character is `1 + χ₀`. Transport along a cardinality
equivalence gives an action on `Fin 11` with precisely the same character.

This construction is independent of the existence proof for the index-eleven
subgroup and of the subsequent sharp-transitivity argument.

Source: Wong (1964), Theorem 6(a), p.108, DOI 10.1017/S1446788700022771.
-/

namespace ABG
noncomputable section

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)

include S hS in
/-- Every index-eleven coset action has permutation character `1 + χ₀`. -/
public theorem ThreeGlobalDegreeData.mathieu_coset_fixedBy_character
    (hG : Nat.card G = 7920) (M : Subgroup G) (hM : M.index = 11) (g : G) :
    (Nat.card (MulAction.fixedBy (G ⧸ M) g) : ℂ) = 1 + c.decomposition.χ 0 g := by
  obtain ⟨θ, hθ, hdθ, heq⟩ := Theory.Character.exists_irreducible_fixedBy_of_min_degree
    (G := G) (X := G ⧸ M) 10 (by decide) hM
    (fun θ hθ hθ1 => c.mathieu_degree_ge_ten hG hθ hθ1)
  have ht (i : Fin 7) := threeInduced_involution_vector S hS c.involution
    c.order_involution c.centralizerEquiv c.decomposition i
  rcases (c.mathieu_degree_ten_iff hG hθ).mp hdθ with h | h | h
  · simpa only [h] using heq g
  · have he := congrArg Complex.re (heq c.involution)
    rw [h, ht] at he
    change (Nat.card (MulAction.fixedBy (G ⧸ M) c.involution) : ℝ) = 1 + (-2 : ℂ).re at he
    norm_num at he
    have hp := Nat.cast_nonneg (α := ℝ) (Nat.card (MulAction.fixedBy (G ⧸ M) c.involution))
    linarith
  · have he := congrArg Complex.re (heq c.involution)
    rw [h, ht] at he
    change (Nat.card (MulAction.fixedBy (G ⧸ M) c.involution) : ℝ) = 1 + (-2 : ℂ).re at he
    norm_num at he
    have hp := Nat.cast_nonneg (α := ℝ) (Nat.card (MulAction.fixedBy (G ⧸ M) c.involution))
    linarith

include S hS in
/-- Transport the eleven-coset action to `Fin 11`, preserving every fixed-point count. -/
public theorem ThreeGlobalDegreeData.exists_mathieu_fin_eleven_action
    (hG : Nat.card G = 7920) (M : Subgroup G) (hM : M.index = 11) :
    ∃ action : MulAction G (Fin 11),
      letI := action
      ∀ g : G, (Nat.card (MulAction.fixedBy (Fin 11) g) : ℂ) =
        1 + c.decomposition.χ 0 g := by
  classical
  let : Fintype (G ⧸ M) := Fintype.ofFinite _
  let e : Fin 11 ≃ (G ⧸ M) :=
    (Fintype.equivFinOfCardEq (by simpa [Subgroup.index, Nat.card_eq_fintype_card] using hM)).symm
  refine ⟨e.mulAction G, ?_⟩
  intro g
  rw [e.card_fixedBy_mulAction g]
  exact c.mathieu_coset_fixedBy_character S hS hG M hM g

end
end ABG
