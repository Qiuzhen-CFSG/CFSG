module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.Preparation
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.ConstituentFlags.Layer

/-!
# The natural chief flags for the exceptional four-space branch

Take the preimage of the natural three-space in the supplied central quotient
of the upper subrepresentation. The quotient map gives a surjection from this
preimage onto that actual natural module, with central kernel. All ambient
displacements lie in the supplied upper space, and their further displacements
lie in the natural preimage. Perfectness therefore makes the quotient by that
preimage central.

`Layer` constructs the literal ambient chief flag and restricts the construction
to each noncentral submodule. Its natural image proves constituent faithfulness;
no ambient indecomposability or offender-generation hypothesis is used.
The final application discharges Preparation's constituent premise on the
original ambient G₂-action. B.4.8(4) itself remains the authorized earlier-source
input, owned by `qt-b-04-natural-extensions`; complement extraction remains
with the exceptional-splitting assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(4),
printed p.91, and the final B.5.6 argument, printed p.110.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit.ExceptionalSplitting
open ConstituentFlags
universe u v
variable {D : Type u} [Group D] {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
  {σ : Representation (ZMod 2) D U}

/-- The preimage of the natural three-space is a central cover containing all
ambient displacements. Perfectness collapses the two central upper layers. -/
theorem CentralFourSection.naturalLayer (s : CentralFourSection σ) :
    Nonempty (Layer σ s.quotientSource.space.toRepresentation) := by
  classical
  let R := s.upper
  let q := s.quotientSource
  let Q := R.toRepresentation.invariants.mkQ
  let P := q.space.toSubmodule.comap Q
  let N : Subrepresentation σ :=
    { toSubmodule := P.map R.toSubmodule.subtype
      apply_mem_toSubmodule g := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨R.toRepresentation g v, ?_, rfl⟩
        exact q.space.apply_mem_toSubmodule g hv }
  have hNR : N ≤ R := Submodule.map_subtype_le _ _
  have hmem (v : R.toSubmodule) : (v : U) ∈ N ↔ Q v ∈ q.space := by
    constructor
    · rintro ⟨w, hw, he⟩
      exact (Subtype.ext he : w = v) ▸ hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  let inc : N.toSubmodule →ₗ[ZMod 2] R.toSubmodule :=
    { toFun := fun v => ⟨v, hNR v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : N.toSubmodule →ₗ[ZMod 2] q.space.toSubmodule :=
    { toFun := fun v => ⟨Q (inc v), (hmem (inc v)).mp v.property⟩
      map_add' := fun a b => Subtype.ext ((Q.comp inc).map_add a b)
      map_smul' := fun a v => Subtype.ext ((Q.comp inc).map_smul a v) }
  have hp : Function.Surjective p := by
    intro w
    obtain ⟨v, hv⟩ := Submodule.mkQ_surjective R.toRepresentation.invariants w.val
    refine ⟨⟨v.val, (hmem v).mpr (hv.symm ▸ w.property)⟩, ?_⟩
    exact Subtype.ext hv
  have he (g : D) (v : N.toSubmodule) :
      p (N.toRepresentation g v) = q.space.toRepresentation g (p v) := rfl
  have hk (v : N.toSubmodule) (hv : p v = 0) (g : D) : σ g v = v := by
    have hz : Q (inc v) = 0 := congrArg Subtype.val hv
    have hf : inc v ∈ R.toRepresentation.invariants :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    exact congrArg Subtype.val (hf g)
  have hdouble (g h : D) (v : U) : σ h (σ g v - v) - (σ g v - v) ∈ N := by
    have hd : σ g v - v ∈ R.toSubmodule :=
      s.moved_le (Submodule.subset_span ⟨g, Subgroup.mem_top _, v, Submodule.mem_top, rfl⟩)
    let d : R.toSubmodule := ⟨σ g v - v, hd⟩
    apply (hmem (R.toRepresentation h d - d)).mpr
    change Q (R.toRepresentation h d - d) ∈ q.space.toSubmodule
    rw [map_sub, q.space_eq]
    exact Submodule.subset_span ⟨h, Subgroup.mem_top _, Q d, Submodule.mem_top, rfl⟩
  let : Group.IsPerfect D := s.isPerfect
  have hcomm : moved N.quotientRepresentation ⊤ ≤ fixedSpace N.quotientRepresentation ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      intro h
      change N.quotientRepresentation h
        (N.toSubmodule.mkQ (σ g v) - N.toSubmodule.mkQ v) =
        N.toSubmodule.mkQ (σ g v) - N.toSubmodule.mkQ v
      rw [← map_sub, Subrepresentation.quotientRepresentation_mk]
      exact (Submodule.Quotient.eq _).mpr (hdouble g h v)
  have hfix := le_fixedSpace_of_commutator_le_fixedSpace N.quotientRepresentation
    (⊤ : Subgroup D) ⊤ (le_subspaceStabilizer _ ⊤ (by simp)) hcomm
  refine ⟨⟨N, p, hp, he, hk, ?_⟩⟩
  intro g v
  exact (Submodule.Quotient.eq N.toSubmodule).mp
    (hfix (show N.toSubmodule.mkQ v ∈ (⊤ : Submodule (ZMod 2) _) from Submodule.mem_top)
      ⟨g, Subgroup.mem_top _⟩)

/-- The actual ambient action has a chief flag with exactly one natural
noncentral section, without any indecomposability assumption. -/
theorem CentralFourSection.uniqueNoncentralNaturalFactor [FiniteDimensional (ZMod 2) U]
    (s : CentralFourSection σ) : UniqueNoncentralNaturalFactor σ := by
  obtain ⟨l⟩ := s.naturalLayer
  exact l.uniqueFactor s.quotientSource.natural

/-- Every noncentral indecomposable submodule is faithful and has the required
literal chief flag. In fact, the construction works for every noncentral submodule. -/
theorem CentralFourSection.constituentApplicability [FiniteDimensional (ZMod 2) U]
    (s : CentralFourSection σ) : ConstituentApplicability σ := by
  let := s.isPerfect
  obtain ⟨l⟩ := s.naturalLayer
  exact l.applicability s.quotientSource.natural

open ComponentReduction
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The original ambient G₂-action meets the exact constituent premises of
B.4.8(4), using the four-space produced by factor extraction. -/
theorem second_constituentApplicability [Finite G] [FiniteDimensional (ZMod 2) V]
    (h483 : EarlierB48Three.{u,v}) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    ConstituentApplicability (secondAmbientAction c) := by
  obtain ⟨s, _⟩ := second_centralFourSection h483 c he f q
  exact s.constituentApplicability

/-- Apply the genuine dimension theorem to the original constituents; the
chief-flag and constituent-faithfulness premises are now discharged. -/
theorem second_smallConstituents_of_fourSection [Finite G] [FiniteDimensional (ZMod 2) V]
    (h483 : EarlierB48Three.{u,v}) (h484 : EarlierB48Four.{u,v}) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    SmallNoncentralConstituents (secondAmbientAction c) :=
  second_smallConstituents h483 h484 c he f q (second_constituentApplicability h483 c he f q)

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit.ExceptionalSplitting
