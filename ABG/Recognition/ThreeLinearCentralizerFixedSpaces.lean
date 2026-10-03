module

public import ABG.Recognition.ThreeLinearLocalData
public import ABG.Recognition.ThreeLinearFixedSpaces
public import Theory.Representation.CharacterFixedDimension
public import Theory.SpecificGroups.GL2.ThreeBorelCensus

/-!
# The two fixed spaces inside Wong's involution centralizer

The actual GL₂(3) equivalence transports its upper-triangular subgroup to
Wong's shared subgroup `T`, of order twelve, inside `C_G(τ)`. The original
degree-twelve character has sums 48 and 96 on these two groups, so their
fixed spaces have dimensions four and two. The order-thirty-six overgroup
of `T` requires the separate Sylow-three construction.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), Appendix (b), pp.109–110, equation (14).
-/

namespace ABG
open BenderGlauberman Matrix Matrix.GeneralLinearGroup
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace ThreeLinearLocalData

variable {G : Type*} [Group G] [Finite G] (c : ThreeLinearLocalData G)

/-- The concrete matrix centralizer, embedded through the supplied equivalence. -/
@[expose] public def centralizerEmbedding : GL (Fin 2) (ZMod 3) →* G :=
  (Subgroup.centralizer ({c.involution} : Set G)).subtype.comp
    (threeCentralizerEquiv c.involution c.centralizerEquiv).symm.toMonoidHom

public theorem centralizerEmbedding_injective : Function.Injective c.centralizerEmbedding :=
  Subtype.val_injective.comp (threeCentralizerEquiv c.involution c.centralizerEquiv).symm.injective

/-- Wong's shared subgroup `T = ⟨τ, μ, ρ⟩`, realized as the transported Borel. -/
@[expose] public def sharedSubgroup : Subgroup G :=
  (GLTwo.borelSubgroup (ZMod 3)).map c.centralizerEmbedding

public theorem sharedSubgroup_le_centralizer :
    c.sharedSubgroup ≤ Subgroup.centralizer ({c.involution} : Set G) := by
  rintro x ⟨a, _, rfl⟩
  exact ((threeCentralizerEquiv c.involution c.centralizerEquiv).symm a).property

/-- The shared subgroup retains its actual upper-triangular matrix model. -/
public def sharedSubgroupEquiv : GLTwo.borelSubgroup (ZMod 3) ≃* c.sharedSubgroup :=
  (GLTwo.borelSubgroup (ZMod 3)).equivMapOfInjective
    c.centralizerEmbedding c.centralizerEmbedding_injective

public theorem centralizer_card :
    Nat.card (Subgroup.centralizer ({c.involution} : Set G)) = 48 := by
  calc
    _ = Nat.card (GL (Fin 2) (ZMod 3)) :=
      Nat.card_congr (threeCentralizerEquiv c.involution c.centralizerEquiv).toEquiv
    _ = 48 := by rw [Matrix.card_GL_field]; decide

public theorem sharedSubgroup_card : Nat.card c.sharedSubgroup = 12 := by
  rw [← Nat.card_congr c.sharedSubgroupEquiv.toEquiv]
  have h := (GLTwo.borelSubgroup (ZMod 3)).index_mul_card
  rw [GLTwo.borelSubgroup_index, Matrix.card_GL_field] at h
  norm_num [Fin.prod_univ_two] at h ⊢
  omega

/-- The original character, pulled back along the actual centralizer embedding. -/
@[expose] public def centralizerCharacter : ClassFunction (GL (Fin 2) (ZMod 3)) :=
  fun x => c.decomposition.χ 5 (c.centralizerEmbedding x)

public theorem centralizerCharacter_isClassFunction : IsClassFunction c.centralizerCharacter :=
  isClassFunction_comp_hom c.centralizerEmbedding
    (irreducibleCharacter_isClassFunction (c.decomposition.irreducible 5))

public theorem centralizerCharacter_values (i : Fin 8) :
    c.centralizerCharacter (threeClassRepr i) = (![12,4,0,3,1,4,0,0] i : ℂ) := by
  have ho := threeCentralizer_class_representative_order c.involution c.centralizerEquiv i
  change orderOf (c.centralizerEmbedding (threeClassRepr i)) = _ at ho
  change c.decomposition.χ 5 (c.centralizerEmbedding (threeClassRepr i)) = _
  rw [c.sixth_values]
  fin_cases i
  · simp [centralizerEmbedding, threeClassRepr]
  · change orderOf (c.centralizerEmbedding (threeClassRepr 1)) = 2 at ho
    have hne : c.centralizerEmbedding (threeClassRepr 1) ≠ 1 := by
      intro h; rw [h, orderOf_one] at ho; norm_num at ho
    simp [hne, ho]
  · change orderOf (c.centralizerEmbedding (threeClassRepr 2)) = 4 at ho
    have hne : c.centralizerEmbedding (threeClassRepr 2) ≠ 1 := by
      intro h; rw [h, orderOf_one] at ho; norm_num at ho
    simp [hne, ho, ThreeLinearPlane.IsPointElement]
  · change orderOf (c.centralizerEmbedding (threeClassRepr 3)) = 3 at ho
    have hne : c.centralizerEmbedding (threeClassRepr 3) ≠ 1 := by
      intro h; rw [h, orderOf_one] at ho; norm_num at ho
    have hc : Nat.card (Subgroup.centralizer
        ({c.centralizerEmbedding (threeClassRepr 3)} : Set G)) = 54 := by
      have h := c.three_class_census.choose_spec.2.2.2.2.1
      rw [c.toThreeGlobalDegreeData.linearUnipotent_eq] at h
      exact h
    have hp : ThreeLinearPlane.IsPointElement G
        (c.centralizerEmbedding (threeClassRepr 3)) := ⟨ho, hc⟩
    simp [hne, ho, hp]
  · change orderOf (c.centralizerEmbedding (threeClassRepr 4)) = 6 at ho
    have hne : c.centralizerEmbedding (threeClassRepr 4) ≠ 1 := by
      intro h; rw [h, orderOf_one] at ho; norm_num at ho
    simp [hne, ho, ThreeLinearPlane.IsPointElement]
  · change orderOf (c.centralizerEmbedding (threeClassRepr 5)) = 2 at ho
    have hne : c.centralizerEmbedding (threeClassRepr 5) ≠ 1 := by
      intro h; rw [h, orderOf_one] at ho; norm_num at ho
    simp [hne, ho]
  · change orderOf (c.centralizerEmbedding (threeClassRepr 6)) = 8 at ho
    have hne : c.centralizerEmbedding (threeClassRepr 6) ≠ 1 := by
      intro h; rw [h, orderOf_one] at ho; norm_num at ho
    simp [hne, ho, ThreeLinearPlane.IsPointElement]
  · change orderOf (c.centralizerEmbedding (threeClassRepr 7)) = 8 at ho
    have hne : c.centralizerEmbedding (threeClassRepr 7) ≠ 1 := by
      intro h; rw [h, orderOf_one] at ho; norm_num at ho
    simp [hne, ho, ThreeLinearPlane.IsPointElement]

public theorem centralizer_character_sum :
    ∑ x : Subgroup.centralizer ({c.involution} : Set G),
      c.decomposition.χ 5 (x : G) = 96 := by
  calc
    _ = ∑ x : GL (Fin 2) (ZMod 3), c.centralizerCharacter x :=
      Fintype.sum_equiv (threeCentralizerEquiv c.involution c.centralizerEquiv).toEquiv
        _ _ (fun x => by simp [centralizerCharacter, centralizerEmbedding])
    _ = _ := by
      rw [three_sum_classFunction _ c.centralizerCharacter_isClassFunction]
      simp_rw [c.centralizerCharacter_values]
      norm_num [Fin.sum_univ_succ]

/-- Averaging the actual degree-twelve representation over the involution centralizer. -/
public theorem centralizer_fixed_dimension :
    Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp
      (Subgroup.centralizer ({c.involution} : Set G)).subtype)) = 2 := by
  apply Representation.finrank_invariants_eq_of_sum_character
  have hχ (x : Subgroup.centralizer ({c.involution} : Set G)) :
      Representation.character (c.sixthRepresentation.comp
        (Subgroup.centralizer ({c.involution} : Set G)).subtype) x =
      c.decomposition.χ 5 (x : G) := by
    rw [c.sixthRepresentation_character]
    rfl
  simp_rw [hχ]
  rw [c.centralizer_character_sum, c.centralizer_card]
  norm_num

/-- The character average on the actual shared subgroup is four. -/
public theorem sharedSubgroup_character_sum :
    ∑ x : c.sharedSubgroup, c.decomposition.χ 5 (x : G) = 48 := by
  calc
    _ = ∑ x : GLTwo.borelSubgroup (ZMod 3), c.centralizerCharacter (x : GL (Fin 2) (ZMod 3)) := by
      symm
      exact Fintype.sum_equiv c.sharedSubgroupEquiv.toEquiv _ _ (fun _ => rfl)
    _ = 48 := three_borel_sum_of_class_values _
      c.centralizerCharacter_isClassFunction c.centralizerCharacter_values

/-- Averaging the actual degree-twelve representation over Wong's shared subgroup. -/
public theorem sharedSubgroup_fixed_dimension :
    Module.finrank ℂ (Representation.invariants
      (c.sixthRepresentation.comp c.sharedSubgroup.subtype)) = 4 := by
  apply Representation.finrank_invariants_eq_of_sum_character
  have hχ (x : c.sharedSubgroup) :
      Representation.character (c.sixthRepresentation.comp c.sharedSubgroup.subtype) x =
      c.decomposition.χ 5 (x : G) := by
    rw [c.sixthRepresentation_character]
    rfl
  simp_rw [hχ]
  rw [c.sharedSubgroup_character_sum, c.sharedSubgroup_card]
  norm_num

end ThreeLinearLocalData
end
end ABG
