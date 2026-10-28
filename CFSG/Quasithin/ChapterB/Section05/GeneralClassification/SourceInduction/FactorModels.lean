module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.GroupTheory.SymmetricNormalQuotients
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.GeneralLinearNatural

/-!
# Intrinsic groups and faithful actions of the actual B.5.6 factors

Each marked factor in the complete B.5.6 two-factor clause is S3, S5, or a
simple perfect binary linear group. The odd-degree restriction on SL3 kills
its scalar center. Thus every factor is center-free and each nontrivial normal
quotient is a 2-group. The literal quotient-image action of each factor is
faithful, including the repeated and exceptional four-dimensional rows.

These source consequences feed intrinsic factor permutation and the original
cyclic rank-one offender selection in G.6.4 and C.5.12. They do not assume a
minimal parabolic, a chosen factor permutation, or a classification conclusion.
Source: Aschbacher–Smith, B.5.6(3), p.105, and G.6.4, pp.345–346.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource

private theorem linear_three_simple_perfect (F : BinaryField) (ho : Odd F.degree)
    {D : Type*} [Group D] (e : D ≃* SL(3,F.Carrier)) :
    IsSimpleGroup D ∧ Group.IsPerfect D := by
  let : IsSimpleGroup PSL(3,F.Carrier) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect SL(3,F.Carrier) := Atlas.sl_perfect 3 (by decide)
  exact ⟨(e.trans (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv
    F.card_eq ho)).isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

private theorem linear_two_group_models (F : BinaryField)
    {D : Type*} [Group D] (e : D ≃* SL(2,F.Carrier)) :
    Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨ (IsSimpleGroup D ∧ Group.IsPerfect D) := by
  by_cases hd : F.degree = 1
  · exact Or.inl ⟨e.trans
      ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
        ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
          BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))⟩
  · have hl : 3 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have hd' : 2 ≤ F.degree := by have := F.degree_pos; omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd'
      norm_num at hp
      omega
    let : IsSimpleGroup PSL(2,F.Carrier) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let : Group.IsPerfect SL(2,F.Carrier) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hl
    exact Or.inr ⟨(e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL)).isSimpleGroup,
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

theorem SourceFactorCase.group_models {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) :
    Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (A ≃* Equiv.Perm (Fin 5)) ∨
      (IsSimpleGroup A ∧ Group.IsPerfect A) := by
  cases h with
  | natural _ hm =>
    cases hm with
    | linearTwo F h =>
      obtain ⟨e⟩ := h
      exact (linear_two_group_models F e.groupEquiv).imp id Or.inr
    | symmetricFive h =>
      obtain ⟨e⟩ := h
      exact Or.inr (Or.inl ⟨e.groupEquiv⟩)
    | linearThree F ho h =>
      obtain ⟨e⟩ := h
      exact Or.inr (Or.inr (linear_three_simple_perfect F ho e.groupEquiv))
  | doubleNatural F ho _ h =>
    obtain ⟨e⟩ := h
    exact Or.inr (Or.inr (linear_three_simple_perfect F ho e.groupEquiv))
  | exceptional _ h =>
    exact Or.inr (Or.inr (linear_three_simple_perfect BinaryField.two (by decide) h.natural.groupEquiv))

private theorem normal_quotient_two_of_equiv {H E : Type*} [Group H] [Group E]
    (e : H ≃* E)
    (hE : ∀ (N : Subgroup E) [N.Normal], N ≠ ⊥ → IsPGroup 2 (E ⧸ N))
    (N : Subgroup H) [N.Normal] (hn : N ≠ ⊥) : IsPGroup 2 (H ⧸ N) := by
  let M := N.map e.toMonoidHom
  let : M.Normal := (inferInstance : N.Normal).map _ e.surjective
  have hM : M ≠ ⊥ := by
    intro hm
    apply hn
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using hm
  exact (hE M hM).of_equiv (QuotientGroup.congr N M e rfl).symm

theorem SourceFactorCase.normal_quotient_two {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) (N : Subgroup A) [N.Normal] (hn : N ≠ ⊥) :
    IsPGroup 2 (A ⧸ N) := by
  rcases h.group_models with he | he | ⟨hs,_⟩
  · obtain ⟨e⟩ := he
    exact normal_quotient_two_of_equiv e symmetric_three_normal_quotient_two N hn
  · obtain ⟨e⟩ := he
    exact normal_quotient_two_of_equiv e (symmetric_normal_quotient_two (by decide : 5 ≤ 5)) N hn
  · let := hs
    exact simple_normal_quotient_two N hn

private theorem center_eq_bot_of_equiv {H E : Type*} [Group H] [Group E]
    (e : H ≃* E) (hz : center E = ⊥) : center H = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have he : e x = 1 := hz.le (by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z))
  exact e.injective (he.trans e.map_one.symm)

theorem SourceFactorCase.center_eq_bot {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) : center A = ⊥ := by
  rcases h.group_models with he | he | ⟨hs,hp⟩
  · obtain ⟨e⟩ := he
    apply center_eq_bot_of_equiv e
    apply (eq_bot_iff_forall _).mpr
    exact by decide
  · obtain ⟨e⟩ := he
    apply center_eq_bot_of_equiv e
    apply le_bot_iff.mp
    apply le_trans (b := centralizer (alternatingGroup (Fin 5) : Set (Equiv.Perm (Fin 5))))
    · intro x hx
      exact mem_centralizer_iff.mpr (fun y _ => mem_center_iff.mp hx y)
    · rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide)]
  · let := hs
    let := hp
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A) inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))

private theorem actionEquiv_faithful {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {σ : Representation (ZMod 2) G X} {τ : Representation (ZMod 2) H Y}
    (e : ActionEquiv σ τ) (hf : Function.Injective τ) : Function.Injective σ := by
  intro a b hab
  apply e.groupEquiv.injective
  apply hf
  ext y
  obtain ⟨x,rfl⟩ := e.linearEquiv.surjective y
  rw [← e.intertwines, ← e.intertwines, hab]

private theorem linearNatural_faithful (F : BinaryField) (n : ℕ) :
    Function.Injective (linearNatural F n) := by
  intro a b hab
  apply specialLinearNatural_injective n
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun hab v

private theorem repeated_faithful {G X : Type*} [Group G]
    [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) G X) (hf : Function.Injective σ) :
    Function.Injective (repeated σ 2) := by
  intro a b hab
  apply hf
  ext x
  exact congrFun (LinearMap.congr_fun hab (fun _ => x)) (0 : Fin 2)

theorem SourceFactorCase.faithful {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) :
    Function.Injective (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) := by
  cases h with
  | natural _ hm =>
    cases hm with
    | linearTwo F h =>
      obtain ⟨e⟩ := h
      exact actionEquiv_faithful e (linearNatural_faithful F 2)
    | symmetricFive h =>
      obtain ⟨e⟩ := h
      exact actionEquiv_faithful e (BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide))
    | linearThree F _ h =>
      obtain ⟨e⟩ := h
      exact actionEquiv_faithful e (linearNatural_faithful F 3)
  | doubleNatural F _ _ h =>
    obtain ⟨e⟩ := h
    exact actionEquiv_faithful e (repeated_faithful _ (linearNatural_faithful F 3))
  | exceptional _ h =>
    have hf := actionEquiv_faithful h.natural (linearNatural_faithful BinaryField.two 3)
    intro a b hab
    apply hf
    apply LinearMap.ext
    intro x
    exact Subtype.ext (LinearMap.congr_fun hab x)


theorem SourceFactorCase.nontrivial {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) : Nontrivial A := by
  rcases h.group_models with he | he | ⟨hs,_⟩
  · obtain ⟨e⟩ := he
    exact e.symm.injective.nontrivial
  · obtain ⟨e⟩ := he
    exact e.symm.injective.nontrivial
  · let := hs
    infer_instance
end CFSG.Quasithin.ChapterB.SourceInduction
