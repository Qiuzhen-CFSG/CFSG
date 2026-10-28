module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Inputs
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Preparing the literal second action for B.4.8(4)

The four-space supplied by factor extraction is transported to
`V₂/C_V₂(G₂)`, using the original quotient maps. Its natural moved submodule
identifies the whole actor with SL₃(2), and proves faithfulness both on the
four-space and on the ambient action.

`ConstituentApplicability` and `SmallNoncentralConstituents` are intermediate
proof obligations, not earlier-source assumptions. The first requires the
literal chief flag from Inputs on every noncentral indecomposable submodule.
Only after that obligation is proved does genuine B.4.8(4) give the second.
No indecomposability of the ambient module or offender-generation transfer is
asserted. The extraction of an ambient complement remains a separate step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(4),
printed p.91, and the final B.5.6 argument, printed p.110.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
namespace ExceptionalSplitting
universe u v

variable {D : Type u} [Group D] {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
  {σ : Representation (ZMod 2) D U}

/-- A central quotient already known to be the B.4.8(3) four-space, inside
an ambient action whose displacements lie in the specified upper space. -/
structure CentralFourSection (σ : Representation (ZMod 2) D U) where
  upper : Subrepresentation σ
  quotientSource : FourDimensionalSource (reducedAction upper.toRepresentation)
  moved_le : moved σ ⊤ ≤ upper.toSubmodule

/-- The actual chief-factor and faithfulness obligations needed for B.4.8(4).
Central indecomposable submodules require no application of that theorem. -/
def ConstituentApplicability (σ : Representation (ZMod 2) D U) : Prop :=
  ∀ S : Subrepresentation σ, IsIndecomposable S.toRepresentation →
    (∀ g v, S.toRepresentation g v = v) ∨
      (Function.Injective S.toRepresentation ∧ UniqueNoncentralNaturalFactor S.toRepresentation)

/-- The dimension bound on actual submodules, not on the whole ambient action. -/
def SmallNoncentralConstituents (σ : Representation (ZMod 2) D U) : Prop :=
  ∀ S : Subrepresentation σ, IsIndecomposable S.toRepresentation →
    (∀ g v, S.toRepresentation g v = v) ∨ Module.finrank (ZMod 2) S.toSubmodule ≤ 4

/-- The natural moved space identifies the entire actor, without a family tag. -/
noncomputable def CentralFourSection.actorEquiv (s : CentralFourSection σ) :
    D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  s.quotientSource.natural.groupEquiv

/-- Perfectness comes from elementary-matrix generation of the actual model;
no simplicity or order certification is needed. -/
theorem CentralFourSection.isPerfect (s : CentralFourSection σ) : Group.IsPerfect D := by
  let := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
  exact Group.IsPerfect.ofSurjective (f := s.actorEquiv.symm.toMonoidHom)
    s.actorEquiv.symm.surjective

theorem four_source_faithful (q : FourDimensionalSource σ) : Function.Injective σ := by
  intro g h he
  apply q.natural.groupEquiv.injective
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := q.natural.linearEquiv.surjective v
  have hw : q.space.toRepresentation g w = q.space.toRepresentation h w :=
    Subtype.ext (LinearMap.congr_fun he w)
  exact (q.natural.intertwines g w).symm.trans
    ((congrArg q.natural.linearEquiv hw).trans (q.natural.intertwines h w))

/-- The natural-bottom four-space has no fixed vectors. A nonzero fixed
space would complement its natural three-space, contradicting indecomposability. -/
theorem four_source_invariants [FiniteDimensional (ZMod 2) U]
    (q : FourDimensionalSource σ) : σ.invariants = ⊥ := by
  have hn : Module.finrank (ZMod 2) q.space.toSubmodule = 3 :=
    q.natural.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))
  have hz := invariants_of_equiv q.natural
    (linearNatural_invariants BinaryField.two (by decide : 2 ≤ 3))
  have hd : Disjoint q.space.toSubmodule σ.invariants := by
    apply Submodule.disjoint_def.mpr
    intro v hv hf
    have hv' : (⟨v,hv⟩ : q.space.toSubmodule) ∈ q.space.toRepresentation.invariants :=
      fun g => Subtype.ext (hf g)
    rw [hz] at hv'
    exact congrArg Subtype.val (show (⟨v,hv⟩ : q.space.toSubmodule) = 0 from hv')
  by_contra hfix
  let : Nontrivial σ.invariants := Submodule.nontrivial_iff_ne_bot.mpr hfix
  have hp : 0 < Module.finrank (ZMod 2) σ.invariants := Module.finrank_pos
  have hdim := q.space.toSubmodule.finrank_sup_add_finrank_inf_eq σ.invariants
  rw [hd.eq_bot, finrank_bot, add_zero, hn] at hdim
  have hle := (q.space.toSubmodule ⊔ σ.invariants).finrank_le
  rw [q.dimension] at hle
  have htop : q.space.toSubmodule ⊔ σ.invariants = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [q.dimension]
    omega
  have hc : IsCompl q.space.toSubmodule (fixed σ).toSubmodule :=
    ⟨hd,codisjoint_iff.mpr htop⟩
  rcases q.indecomposable.2 q.space (fixed σ) hc with h | h
  · rw [h] at hn
    change Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) U) = 3 at hn
    simp at hn
  · exact hfix (congrArg Subrepresentation.toSubmodule h)

/-- Every nonzero submodule contains the natural moved space. This essential
socle assertion concerns the actual four-space, not an ambient complement. -/
theorem four_source_submodule_contains_natural [FiniteDimensional (ZMod 2) U]
    (q : FourDimensionalSource σ) (A : Subrepresentation σ) (hA : A ≠ ⊥) :
    q.space ≤ A := by
  let := irreducible_of_equiv q.natural
    (linearNatural_irreducible BinaryField.two (by decide : 2 ≤ 3))
  have hn : IsAtom q.space := Subrepresentation.irreducible_iff_isAtom q.space |>.mp inferInstance
  by_contra h
  have hd : Disjoint q.space.toSubmodule A.toSubmodule := by
    have h' := hn.not_le_iff_disjoint.mp h
    rw [disjoint_iff] at h' ⊢
    exact congrArg Subrepresentation.toSubmodule h'
  apply hA
  apply Subrepresentation.toSubmodule_injective
  apply bot_unique
  intro v hv
  have hf : v ∈ σ.invariants := by
    intro g
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hd (σ g v - v)
    · rw [q.space_eq]
      exact Submodule.subset_span ⟨g,Subgroup.mem_top _,v,Submodule.mem_top,rfl⟩
    · exact A.toSubmodule.sub_mem (A.apply_mem_toSubmodule g hv) hv
  rwa [four_source_invariants q] at hf

/-- Faithfulness lifts through the literal submodule and fixed quotient. -/
theorem CentralFourSection.faithful (s : CentralFourSection σ) :
    Function.Injective σ := by
  intro g h he
  apply four_source_faithful s.quotientSource
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change (Representation.invariants s.upper.toRepresentation).mkQ
        (s.upper.toRepresentation g v) =
      (Representation.invariants s.upper.toRepresentation).mkQ
        (s.upper.toRepresentation h v)
    congr 1
    exact Subtype.ext (LinearMap.congr_fun he v)

/-- This is the genuine dimension conclusion of B.4.8(4), applied separately
to each noncentral indecomposable constituent. The flag premise still needs
its producer; this conditional result does not assert an ambient splitting. -/
theorem smallConstituents_of_applicability [Finite D] [FiniteDimensional (ZMod 2) U]
    (h48 : EarlierB48Four.{u,v}) (s : CentralFourSection σ)
    (ha : ConstituentApplicability σ) : SmallNoncentralConstituents σ := by
  intro S hS
  rcases ha S hS with ht | ⟨hf,hn⟩
  · exact Or.inl ht
  · right
    rcases h48 D S.toSubmodule S.toRepresentation hf hS ⟨s.actorEquiv⟩ hn with h | h
    · omega
    · omega

open ComponentReduction
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- G₂ acts here on the original ambient V. -/
abbrev secondAmbientAction (c : Conclusion ρ) : Representation (ZMod 2) (second c) V :=
  ρ.comp (second c).subtype

/-- V₂ as a subrepresentation for that same ambient G₂-action. -/
def secondUpper (c : Conclusion ρ) : Subrepresentation (secondAmbientAction c) where
  toSubmodule := c.productConfiguration.fixed.toSubmodule
  apply_mem_toSubmodule g := c.productConfiguration.fixed.apply_mem_toSubmodule g

/-- Transport from the supplied factor quotient to the whole fixed quotient
of V₂; both intermediate maps are the published literal quotient maps. -/
theorem second_reduced_source [Finite G] [FiniteDimensional (ZMod 2) V]
    (h48 : EarlierB48Three.{u,v}) (c : Conclusion ρ)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    Nonempty (FourDimensionalSource (reducedAction (secondAction c))) := by
  obtain ⟨q'⟩ := four_source_transport h48 (actionSymm (factorQuotientEquiv c f)) q
  exact four_source_transport h48 (secondQuotientEquiv c) q'

/-- The actual B.5.6 input to the constituent and splitting arguments. -/
theorem second_centralFourSection [Finite G] [FiniteDimensional (ZMod 2) V]
    (h48 : EarlierB48Three.{u,v}) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    ∃ s : CentralFourSection (secondAmbientAction c), s.upper = secondUpper c := by
  obtain ⟨q'⟩ := second_reduced_source h48 c f q
  refine ⟨⟨secondUpper c,q',?_⟩,rfl⟩
  apply Submodule.span_le.mpr
  rintro _ ⟨g,_,v,_,rfl⟩
  apply second_moved_le_fixed c he
  exact Submodule.subset_span ⟨g,g.property,v,Submodule.mem_top,rfl⟩

/-- The transported four-space proves faithfulness of the actual ambient
second action; faithfulness is not inferred from a group-family label. -/
theorem second_ambient_faithful [Finite G] [FiniteDimensional (ZMod 2) V]
    (h48 : EarlierB48Three.{u,v}) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    Function.Injective (secondAmbientAction c) := by
  obtain ⟨s,_⟩ := second_centralFourSection h48 c he f q
  exact s.faithful

/-- Source application of the indecomposable dimension theorem, with the
unproved chief-flag transfer displayed as an intermediate premise. -/
theorem second_smallConstituents [Finite G] [FiniteDimensional (ZMod 2) V]
    (h483 : EarlierB48Three.{u,v}) (h484 : EarlierB48Four.{u,v}) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f))
    (ha : ConstituentApplicability (secondAmbientAction c)) :
    SmallNoncentralConstituents (secondAmbientAction c) := by
  obtain ⟨s,_⟩ := second_centralFourSection h483 c he f q
  exact smallConstituents_of_applicability h484 s ha

/-- A G₂-submodule lying in C_V(G₁) is an ambient G-submodule. This uses the
literal product decomposition, not an assumption of ambient invariance. -/
def ambientModule (c : Conclusion ρ) (S : Subrepresentation (secondAmbientAction c))
    (hS : S ≤ secondUpper c) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule g v hv := by
    obtain ⟨a,b,rfl⟩ := c.productConfiguration.product.exists_mul g
    have hb : ρ (b : G) v ∈ S.toSubmodule := S.apply_mem_toSubmodule b hv
    have hf : ρ (b : G) v ∈ fixedSpace ρ c.first := by
      rw [← c.productConfiguration.fixed_eq]
      exact hS hb
    rw [map_mul, Module.End.mul_apply,
      show ρ (a : G) (ρ (b : G) v) = ρ (b : G) v from hf a]
    exact hb

end ExceptionalSplitting
end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
