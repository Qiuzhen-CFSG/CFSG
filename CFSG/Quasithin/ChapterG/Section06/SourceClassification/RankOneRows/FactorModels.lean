module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.RankOneRows.ModelDisplacement
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# The genuine small quotient models for a marked B.5.6 factor

The displacement of the original rank-one involution decreases on the literal
quotient image. Faithfulness of that factor action keeps it nonzero. Doubled
natural and exceptional four-dimensional rows have larger displacement and
are excluded. In the natural linear rows the same marked element forces the
defining field to be F2, giving precisely the S3, SL3(2), and S5 modules used
by G.6.4's two-factor reconstruction. The original moved-space equality is
retained; no replacement subspace or action is selected.

Source: Aschbacher–Smith G.6.4, p.346, using B.5.6(3), p.105.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V}

private theorem binary_natural_of_rank_one
    {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X] {σ : Representation (ZMod 2) H X}
    (hf : Function.Injective σ) (t : H) (hne : t ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) ≤ 1)
    (F : BinaryField) (n : ℕ) (hn : IsLinearNatural σ F n) :
    IsLinearNatural σ BinaryField.two n := by
  obtain ⟨e⟩ := hn
  have hF := model_field_degree_one_of_rank_one F hf t hne hr (specialLinearNatural n) e
  let eF := ExtensionConsequences.degreeOneNaturalEquiv F hF n
  refine ⟨⟨e.groupEquiv.trans eF.groupEquiv,e.linearEquiv.trans eF.linearEquiv,?_⟩⟩
  intro g v
  exact (congrArg eF.linearEquiv (e.intertwines g v)).trans
    (eF.intertwines (e.groupEquiv g) (e.linearEquiv v))

/-- Source B.5.6's factor row with every rank-one model selection discharged
on the original quotient image, using the original ambient involution. -/
theorem sourceFactor_small_quotient_of_rank_one
    {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) (t : D) (hA : t ∈ A)
    (ht : t ^ 2 = 1) (hne : t ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) :
    U.toSubmodule = moved ρ A ∧
      (IsLinearNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)
        BinaryField.two 2 ∨
       IsLinearNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)
        BinaryField.two 3 ∨
       IsSymmetricNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) 5) := by
  let τ := (fixed ρ).quotientRepresentation
  let W := (fixed ρ).quotientImage U
  let σ := W.toRepresentation.comp A.subtype
  let tA : A := ⟨t,hA⟩
  have htA : tA ≠ 1 := fun he => hne (congrArg Subtype.val he)
  have hf : Function.Injective σ := h.faithful
  have hcostle : Module.finrank (ZMod 2) (LinearMap.range (σ tA - LinearMap.id)) ≤ 1 := by
    have h₁ := fixedCodim_subrepresentation_le τ W (zpowers t)
    have h₂ := fixedCodim_quotient_add_subrepresentation_le ρ (fixed ρ) (zpowers t)
    simp only [fixedCodim_zpowers_eq_displacement_rank] at h₁ h₂
    exact h₁.trans ((Nat.le_add_right _ _).trans h₂) |>.trans hr
  have hpositive := fixedCodim_pos_of_faithful σ hf
    (show zpowers tA ≠ ⊥ by intro he; exact htA (he.le (mem_zpowers tA)))
  simp only [fixedCodim_zpowers_eq_displacement_rank] at hpositive
  have hcost : Module.finrank (ZMod 2) (LinearMap.range (σ tA - LinearMap.id)) = 1 := by omega
  cases h with
  | natural hm hn =>
    refine ⟨hm,?_⟩
    cases hn with
    | linearTwo F hn =>
      exact Or.inl (binary_natural_of_rank_one hf tA htA hcostle F 2 hn)
    | linearThree F _ hn =>
      exact Or.inr (Or.inl (binary_natural_of_rank_one hf tA htA hcostle F 3 hn))
    | symmetricFive hn => exact Or.inr (Or.inr hn)
  | doubleNatural F _ _ hn =>
    obtain ⟨e⟩ := hn
    have he := (e.displacement_rank tA).symm.trans hcost
    have hd := repeated_displacement_rank (linearNatural F 3) 2 (e.groupEquiv tA)
    omega
  | exceptional _ e =>
    have hp : tA ^ 2 = 1 := Subtype.ext ht
    have ho : orderOf tA = 2 := orderOf_eq_prime hp htA
    have hd : Module.finrank (ZMod 2) (fixedSpace σ (zpowers tA)) = 2 :=
      (e.involutions tA ho).2.1
    have hdim : Module.finrank (ZMod 2) W.toSubmodule = 4 := e.dimension
    have hc := fixedCodim_add_finrank σ (zpowers tA)
    rw [hd, hdim, fixedCodim_zpowers_eq_displacement_rank, hcost] at hc
    omega
end CFSG.Quasithin.ChapterG.Section06
