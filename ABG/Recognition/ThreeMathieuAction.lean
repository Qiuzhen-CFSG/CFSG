module

public import ABG.Recognition.ThreeMathieuLocalConfiguration
public import ABG.Recognition.ThreeMathieuIndexEleven
public import ABG.Recognition.ThreeMathieuCosetCharacter
public import Theory.GroupTheory.SharpTransitivityFixedPoints

/-!
# Wong's faithful sharply four-transitive degree-eleven action

The cyclic four-complement in a Sylow-five normalizer lies in a quaternion
eight-subgroup. Fixed-space dimensions for the same first character show
that their join is proper. The quaternion obstruction excludes order 120,
so this join has index eleven. Its coset character is `1 + χ₀`.
The first character's values imply that a nonidentity element fixes at most three
points. Thus the action is faithful and free on ordered four-tuples. The
order `7920 = 11 * 10 * 9 * 8` makes this action sharply four-transitive.

Source: Wong (1964), Theorem 6(a), pp.107–108,
DOI 10.1017/S1446788700022771.
-/

namespace ABG
noncomputable section

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (c : ThreeGlobalDegreeData G) (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S) (hG : Nat.card G = 7920)

include S hS hG

/-- The character `1 + χ₀` allows no nonidentity element to fix four points. -/
public theorem ThreeGlobalDegreeData.mathieu_fixedBy_lt_four
    {α : Type*} [MulAction G α]
    (hchar : ∀ g : G, (Nat.card (MulAction.fixedBy α g) : ℂ) =
      1 + c.decomposition.χ 0 g) (g : G) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy α g) < 4 := by
  have h := hchar g
  rw [c.first_character_values S hS hG g] at h
  have hone : orderOf g ≠ 1 := fun ho => hg (orderOf_eq_one_iff.mp ho)
  simp only [if_neg hone] at h
  generalize hn : Nat.card (MulAction.fixedBy α g) = n at h ⊢
  split_ifs at h <;> norm_num at h <;> norm_cast at h <;> omega

/-- The final counting step for an eleven-point action with Wong's character. -/
public theorem ThreeGlobalDegreeData.mathieu_action_sharp_of_fixedBy_character
    [MulAction G (Fin 11)]
    (hchar : ∀ g : G, (Nat.card (MulAction.fixedBy (Fin 11) g) : ℂ) =
      1 + c.decomposition.χ 0 g) :
    FaithfulSMul G (Fin 11) ∧
      Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 11) 4 := by
  have hfix := c.mathieu_fixedBy_lt_four S hS hG hchar
  refine ⟨Theory.GroupTheory.MulAction.faithfulSMul_of_fixedBy_lt (by decide) hfix, ?_⟩
  apply Theory.GroupTheory.MulAction.isSharplyMultiplyPretransitive_of_fixedBy_lt
    (Fin.castLEEmb (by decide : 4 ≤ 11)) hfix
  simpa using hG

include c in
/-- The local configuration supplies an actual subgroup of index eleven. -/
public theorem ThreeGlobalDegreeData.exists_mathieu_index_eleven :
    ∃ M : Subgroup G, M.index = 11 := by
  let P : Sylow 5 G := Classical.choice inferInstance
  obtain ⟨F, Q, e, ρ, _, _, _, _, _, _, _, _, _, _, _, hproper⟩ :=
    c.exists_mathieu_local_configuration S hS hG P
  exact ⟨Q ⊔ Subgroup.normalizer (P : Set G),
    c.mathieu_index_eleven S hS hG P Q _ e le_sup_left le_sup_right hproper⟩

/-- The eleven-coset action, retaining the shared first-character identity,
is faithful and sharply four-transitive. -/
public theorem ThreeGlobalDegreeData.exists_mathieu_sharp_action :
    ∃ action : MulAction G (Fin 11),
      letI := action
      FaithfulSMul G (Fin 11) ∧
      Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 11) 4 ∧
      ∀ g : G, (Nat.card (MulAction.fixedBy (Fin 11) g) : ℂ) =
        1 + c.decomposition.χ 0 g := by
  obtain ⟨M, hM⟩ := c.exists_mathieu_index_eleven S hS hG
  obtain ⟨action, hchar⟩ := c.exists_mathieu_fin_eleven_action S hS hG M hM
  let := action
  obtain ⟨hfaithful, hsharp⟩ := c.mathieu_action_sharp_of_fixedBy_character S hS hG hchar
  exact ⟨action, hfaithful, hsharp, hchar⟩

/-- Wong's Theorem 6(a): the original local hypotheses in the order-7920
branch construct a faithful sharply four-transitive action on eleven points. -/
public theorem exists_mathieu_sharply_four_transitive_action
    (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    ∃ action : MulAction G (Fin 11),
      letI := action
      FaithfulSMul G (Fin 11) ∧
      Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 11) 4 := by
  obtain ⟨c⟩ := exists_threeCharacterTheory S hS hcard hC
  obtain ⟨action, hfaithful, hsharp, _⟩ := c.exists_mathieu_sharp_action S hS hG
  exact ⟨action, hfaithful, hsharp⟩

end
end ABG
