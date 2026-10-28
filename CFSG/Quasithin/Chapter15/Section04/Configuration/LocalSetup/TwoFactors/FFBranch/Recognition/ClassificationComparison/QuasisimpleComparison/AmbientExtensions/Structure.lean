module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Targets
public import Theory.GroupTheory.GeneralizedFitting.NormalTwoTower

/-!
# The embedded component in the ambient FF comparison

B.5.1(1) supplies a two-group quotient of the offender actor by its
generalized Fitting subgroup. The actual ambient two-group quotient then
identifies the image of this component with both F*(D) and O²(D).
The accompanying isomorphism commutes with the two original inclusions.
Model transport below retains the original representation on the image of N.

These are structural reductions, not an ambient classification.
Source: Aschbacher–Smith, B.5.1(1), p.99; F.6.18, pp.309–310;
15.4.18, p.1163 (combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace QuasisimpleComparison
universe u v w

variable {A : Type u} [Group A] [Finite A]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {σ : Representation (ZMod 2) A V}

/-- The supplement in B.5.1(1) is enough to construct the actual quotient. -/
theorem BoundedBranch.actorQuotient_twoGroup (b : BoundedBranch σ) :
    IsPGroup 2 (A ⧸ generalizedFitting A) := by
  have whole (he : generalizedFitting A = ⊤) :
      IsPGroup 2 (A ⧸ generalizedFitting A) := by
    let : Subsingleton (A ⧸ (⊤ : Subgroup A)) := QuotientGroup.subsingleton_quotient_top
    exact (IsPGroup.of_subsingleton 2 (A ⧸ (⊤ : Subgroup A))).of_equiv
      (QuotientGroup.quotientMulEquivOfEq he).symm
  cases b.source.clause_one with
  | irreducible _ _ _ _ he =>
    rcases he with he | ⟨he, _⟩
    · exact whole he
    · let S : Sylow 2 A := default
      exact quotient_isPGroup_of_sup_eq_top (S : Subgroup A)
        (generalizedFitting A) S.isPGroup' (by simpa only [sup_comm] using he S)
  | doubleThree _ he _ _ _ => exact whole he
  | naturalDual _ _ he _ => exact whole he
  | repeatedNatural _ _ _ _ _ he _ => exact whole he

namespace AmbientExtensions
attribute [local instance] offenderSubgroup_normal
variable {D : Type u} [Group D] [Finite D]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D} {K : GroupClass.{u}}

/-- The component of the offender actor is embedded using its literal subtype. -/
abbrev componentImage (ρ : Representation (ZMod 2) D V) : Subgroup D :=
  (generalizedFitting (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype

/-- Relative normality upgrades to normality in D through the two-residual. -/
theorem componentImage_normal
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) :
    (componentImage ρ).Normal := by
  let := b.quasisimple
  exact normalTwoTower_normal _ _ b.actorQuotient_twoGroup

/-- The two successive source quotients give D/F*(N), with its actual kernel. -/
theorem componentImage_quotient_twoGroup
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) :
    letI := componentImage_normal b
    IsPGroup 2 (D ⧸ componentImage ρ) := by
  let := b.quasisimple
  exact normalTwoTower_quotient _ _ b.actorQuotient_twoGroup h.quotient_twoGroup

/-- Both sides are subgroups of the original ambient group. -/
theorem fitting_eq_componentImage
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) :
    generalizedFitting D = componentImage ρ := by
  let := b.quasisimple
  exact normalTwoTower_fitting _ _ b.actorQuotient_twoGroup h.quotient_twoGroup h.twoCore

/-- O² is the residual, not the two-core, in F.6.18(3). -/
theorem residual_eq_componentImage
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) :
    pResidual 2 D = componentImage ρ := by
  let := b.quasisimple
  exact normalTwoTower_residual _ _ b.actorQuotient_twoGroup h.quotient_twoGroup

/-- The actor component and ambient component have the compatible inclusion. -/
noncomputable def componentEquiv
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) :
    generalizedFitting (offenderSubgroup ρ) ≃* generalizedFitting D :=
  ((generalizedFitting (offenderSubgroup ρ)).equivMapOfInjective
    (offenderSubgroup ρ).subtype (offenderSubgroup ρ).subtype_injective).trans
    (MulEquiv.subgroupCongr (fitting_eq_componentImage h b).symm)

/-- The abstract component isomorphism uses exactly N ≤ D. -/
theorem componentEquiv_coe
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (x : generalizedFitting (offenderSubgroup ρ)) :
    (componentEquiv h b x : D) = ((x : offenderSubgroup ρ) : D) := rfl

/-- The ambient component inherits the actor's actual bounded component model. -/
theorem ambient_boundedComponent
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) :
    BoundedQuasisimpleModel (generalizedFitting D) :=
  b.component.comap (componentEquiv h b).symm

variable {M : Type w} [Group M]

/-- Mark the original offender subgroup under any subsequently constructed
ambient model equivalence. -/
noncomputable def offenderEquiv (e : D ≃* M) :
    offenderSubgroup ρ ≃* (offenderSubgroup ρ).map e.toMonoidHom :=
  e.subgroupMap (offenderSubgroup ρ)

omit [Finite D] in
/-- This marking commutes with the original ambient equivalence. -/
theorem offenderEquiv_coe (e : D ≃* M) (x : offenderSubgroup ρ) :
    (offenderEquiv (ρ := ρ) e x : M) = e (x : D) := rfl

omit [Finite D] in
/-- Restricting the transported ambient representation to the marked image
and pulling it back recovers rho on the actual N. -/
theorem marked_restriction (e : D ≃* M) :
    ((ρ.comp e.symm.toMonoidHom).comp
      ((offenderSubgroup ρ).map e.toMonoidHom).subtype).comp
        (offenderEquiv (ρ := ρ) e).toMonoidHom =
      ρ.comp (offenderSubgroup ρ).subtype := by
  ext x v
  change ρ (e.symm (e (x : D))) v = ρ (x : D) v
  rw [e.symm_apply_apply]

omit [Finite D] in
/-- Normality of the marked offender image in the constructed model. -/
theorem offenderImage_normal (e : D ≃* M) :
    ((offenderSubgroup ρ).map e.toMonoidHom).Normal :=
  (offenderSubgroup_normal ρ).map e.toMonoidHom e.surjective

/-- The quotient equivalence uses precisely the marked offender image. -/
noncomputable def offenderQuotientEquiv (e : D ≃* M) :
    letI := offenderImage_normal (ρ := ρ) e
    D ⧸ offenderSubgroup ρ ≃* M ⧸ (offenderSubgroup ρ).map e.toMonoidHom := by
  let := offenderImage_normal (ρ := ρ) e
  exact QuotientGroup.congr _ _ e rfl

omit [Finite D] in
/-- The two quotient maps commute with the ambient model equivalence. -/
theorem offenderQuotientEquiv_mk (e : D ≃* M) (x : D) :
    letI := offenderImage_normal (ρ := ρ) e
    offenderQuotientEquiv (ρ := ρ) e (QuotientGroup.mk' (offenderSubgroup ρ) x) =
      QuotientGroup.mk' ((offenderSubgroup ρ).map e.toMonoidHom) (e x) := rfl

omit [Finite D] in
/-- The derived subgroup is transported with the actual two inclusion maps. -/
theorem marked_derived (e : D ≃* M) :
    ((commutator (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype).map e.toMonoidHom =
      (commutator ((offenderSubgroup ρ).map e.toMonoidHom)).map
        ((offenderSubgroup ρ).map e.toMonoidHom).subtype := by
  rw [map_commutator_eq, range_subtype, Subgroup.map_commutator,
    map_commutator_eq, range_subtype]

omit [Finite D] in
/-- The literal centralizer of N is carried to the centralizer of its marked image. -/
theorem marked_centralizer (e : D ≃* M) :
    (centralizer (offenderSubgroup ρ : Set D)).map e.toMonoidHom =
      centralizer ((offenderSubgroup ρ).map e.toMonoidHom : Set M) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) ⟨y, hy, rfl⟩

end AmbientExtensions
end QuasisimpleComparison
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
