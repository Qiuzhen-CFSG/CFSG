module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved.NoFF
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.NativeRecognition
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleSections

/-!
# Irreducible FF sections of the actual multiplicity action

For a faithful FF module with centerless quasisimple generalized Fitting
subgroup, select a minimal best offender. The proved B.1.5 stabilization
theorem makes it preserve an actual Irr⁺ constituent. Its generated overgroup
acts on the literal central quotient, which remains FF. The quotient above
the component is a two-group, and the original component embeds in the
faithful section action image and becomes its entire generalized Fitting
subgroup. Thus all native B.4 hypotheses are derived.

The corrected native classifier then excludes the even-degree unitary
component, without assuming irreducibility of the initial module. The actual
original multiplicity construction and its source application are in
OriginalSource.Multiplicity and OriginalSource.Unitary; remaining external
linear and exceptional branches belong to qt-d-138-fields-source.
Source: Aschbacher–Smith, B.1.5, B.1.11, B.4.2 and 13.8.20(a),
printed pp.69–73,86,954.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

local instance centralQuotientFinite (ρ : Representation (ZMod 2) D V)
    (K : Subgroup D) (I : Submodule (ZMod 2) V) : Finite (centralQuotient ρ K I) :=
  Finite.of_surjective _ (Submodule.mkQ_surjective ((fixedSpace ρ K).comap I.subtype))

/-- Select an actual irreducible FF central section of a faithful FF module
whose generalized Fitting subgroup is a centerless quasisimple group. The
component is retained through the literal section action image. -/
theorem faithful_irreducible_ff_section
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (K : Subgroup D) [K.Normal] [IsQuasisimple K]
    (hfit : generalizedFitting D = K) (hz : center K = ⊥)
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hff : IsFFModule ρ) :
    ∃ (B : Subgroup D) (I : Submodule (ZMod 2) V),
      IsMinimalBestOffender ρ B ∧ IsIrrPlus ρ K I ∧
      ∃ (hI : K ⊔ B ≤ subspaceStabilizer ρ I),
        let τ := centralSectionRepresentation ρ K (K ⊔ B) I hI le_normalizer_of_normal
        B4Hypotheses KnownSimple.IsKnownSimple (imageRepresentation τ) ∧
        IsFFModule (imageRepresentation τ) ∧
        generalizedFitting (actionImage τ) = actionSubgroup τ (K.subgroupOf (K ⊔ B)) ∧
        Nonempty (K ≃* generalizedFitting (actionImage τ)) := by
  have hcent := LinearTwo.NoStrongMoved.selfcentral_of_fitting K hfit hz
  have hcore : pCore 2 D = ⊥ := by
    apply bot_unique
    rw [←hcent]
    exact ChapterB.irreducibleReduction_core_centralizes K
  obtain ⟨A,hA⟩ := hff
  obtain ⟨B,_,hB,_,_⟩ := hA.exists_quadratic_minimalBestOffender ρ
  let : IsElementaryAbelian 2 B := hB.1.1.2
  have hp := IsElementaryAbelian.isPGroup 2 B
  have hq : IsQuasisimple (generalizedFitting D) := hfit.symm ▸ inferInstance
  have hcomm : ⁅K,B⁆ = K := by
    simpa only [hfit] using ChapterB.QuasisimpleSections.commutator_fitting_eq hcore hq hB.1.1.1 hp
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_faithful ρ hf K ((nontrivial_iff_ne_bot K).mp inferInstance)
  obtain ⟨hr,hchief⟩ := LinearTwo.NoStrongMoved.quasisimple_stabilization_hypotheses K
  have hBI := ChapterB.source_lemma_B_1_5_3 ρ hf hB hr hcomm hchief hI
  let J := K ⊔ B
  let L := K.subgroupOf J
  have hJI : J ≤ subspaceStabilizer ρ I := sup_le hI.choose hBI
  let τ := centralSectionRepresentation ρ K J I hJI le_normalizer_of_normal
  let : Finite (centralQuotient ρ K I) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective ((fixedSpace ρ K).comap I.subtype))
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe (show K ≤ J from le_sup_left)).symm
  have hsurvive : ¬ L ≤ (actionHom τ).ker := by
    intro hk
    apply hI.not_le_fixedSpace ρ
    rw [←hI.choose_spec.1]
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hkK,v,hv,rfl⟩
    have he := (actionHom_eq_one_iff τ (⟨k,mem_sup_left hkK⟩ : J)).mp (hk hkK)
      (Submodule.Quotient.mk (⟨v,hv⟩ : I))
    exact (Submodule.Quotient.eq ((fixedSpace ρ K).comap I.subtype)).mp he
  have hi : IsIrreducible (τ.comp L.subtype) := by
    let e : L ≃* K := subgroupOfEquivOfLe le_sup_left
    apply (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mp
    exact hI.choose_spec.2
  have hzL : center L = ⊥ := by
    let e : L ≃* K := subgroupOfEquivOfLe le_sup_left
    apply _root_.eq_bot_iff.mpr
    intro k hk
    have hh := (centerCongr e ⟨k,hk⟩).property
    change e k ∈ center K at hh
    rw [hz,mem_bot] at hh
    exact mem_bot.mpr (e.injective (hh.trans e.map_one.symm))
  have hquot := local_quotient_isTwoGroup K B hp
  obtain ⟨hq',hi',hfit'⟩ := SourceOrbit.ActionImage.Structure.image_structure τ L hsurvive hquot hi
  have hB4 : B4Hypotheses KnownSimple.IsKnownSimple (imageRepresentation τ) := by
    refine ⟨SourceOrbit.ActionImage.Structure.image_sqtk τ L hsurvive (hS.subgroup J) hquot hzL,
      imageRepresentation_injective τ,?_,?_⟩
    · rw [hfit']; exact hq'
    · rw [hfit']; exact hi'
  have hdis : Disjoint B (centralizer (K : Set D)) := by rw [hcent]; exact disjoint_bot_right
  have hFF := centralSection_isFFModule_of_offender ρ K B J hB.1 le_sup_left le_sup_right
    hdis I hI hJI le_normalizer_of_normal
  let e : K ≃* actionSubgroup τ L :=
    (subgroupOfEquivOfLe (show K ≤ J from le_sup_left)).symm.trans
      (SourceOrbit.ActionImage.Structure.componentEquiv τ L hsurvive hzL)
  exact ⟨B,I,hB,hI,hJI,hB4,hFF,hfit',⟨e.trans (MulEquiv.subgroupCongr hfit'.symm)⟩⟩

/-- A faithful FF module with centerless quasisimple generalized Fitting
subgroup cannot have an even-degree unitary component. Irreducibility of the
original module is not assumed: replacement supplies the classified section. -/
theorem unitary_not_ff_of_centerless_fitting
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (K : Subgroup D) [K.Normal] [IsQuasisimple K]
    (hfit : generalizedFitting D = K) (hz : center K = ⊥)
    (hS : IsSQTK KnownSimple.IsKnownSimple D)
    {Q : Type*} [Field Q] [Finite Q]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 Q)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (hQ : Nat.card Q = 2 ^ (2*n))
    (hconj : ∀ x, J.conj x = x ^ (2^n))
    (e : K ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    ¬ IsFFModule ρ := by
  intro hff
  obtain ⟨B,I,_,_,hI,hB4,hFF,_,⟨b⟩⟩ :=
    faithful_irreducible_ff_section ρ hf K hfit hz hS hff
  exact NativeRecognition.unitary_not_ff _ hB4 J hn heven hQ hconj (b.symm.trans e) hFF


/-- Keep the original component marking when adjoining the source offender.
This boundary avoids rebuilding the induced section action during transport. -/
theorem unitary_not_ff_of_generated_fitting
    (K A : Subgroup D) [IsQuasisimple K]
    (ρ : Representation (ZMod 2) (K ⊔ A : Subgroup D) V) (hf : Function.Injective ρ)
    (hfit : generalizedFitting (K ⊔ A : Subgroup D) = K.subgroupOf (K ⊔ A))
    (hz : center K = ⊥) (hS : IsSQTK KnownSimple.IsKnownSimple (K ⊔ A : Subgroup D))
    {Q : Type*} [Field Q] [Finite Q]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 Q)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (hQ : Nat.card Q = 2 ^ (2*n))
    (hconj : ∀ x, J.conj x = x ^ (2^n))
    (e : K ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    ¬ IsFFModule ρ := by
  let K₀ := K.subgroupOf (K ⊔ A)
  let b : K₀ ≃* K := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv b.symm
  have hfit₀ : generalizedFitting (K ⊔ A : Subgroup D) = K₀ := hfit
  let : K₀.Normal := hfit₀ ▸ generalizedFitting_normal
  have hz₀ : center K₀ = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro k hk
    have hh := (centerCongr b ⟨k,hk⟩).property
    change b k ∈ center K at hh
    rw [hz,mem_bot] at hh
    exact mem_bot.mpr (b.injective (hh.trans b.map_one.symm))
  exact unitary_not_ff_of_centerless_fitting ρ hf K₀ hfit₀ hz₀ hS
    J hn heven hQ hconj (b.trans e)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
