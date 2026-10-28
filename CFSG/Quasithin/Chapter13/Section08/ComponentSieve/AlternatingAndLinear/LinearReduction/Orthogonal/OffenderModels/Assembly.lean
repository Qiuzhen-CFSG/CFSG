module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.TransvectionSections

/-!
# The three source offender-model alternatives in 13.8.25

Start with a maximal proper submodule of the actual conjugation section
U_H/V₁, its marked natural S₈ quotient, and nontrivial K-action on the
submodule. The earlier group equality U_H = [U_H,K] supplies full linear
commutator generation and faithfulness of both sections.

The strong-quotient case identifies the whole actor with the four independent
transpositions, bounds the submodule's fixed codimension by five, and recognizes
its literal commutator. In the strong-submodule case the same constituent and
extension deductions construct that model first. The critical-subspace sieve
then proves A₁ is outside the subgroup preimage of W: containment would force
quotient codimension to equal actor rank, contradicting three versus four.

When neither section has a strong best offender contained in the actor,
intrinsic transvection geometry gives rank one. The augmentation map constructs
the literal [W,K] model. All models, actors and components share one permutation
marking, and both source positions of the critical line are retained.

The only classification premises are the universal earlier B.4 inputs with
faithfulness, component irreducibility, quadraticity and ratio bounds explicit.
The chosen maximal submodule and natural quotient are supplied witnesses; no
new section recognition is assumed. The terminal exclusion belongs to the
parent orthogonal argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.21–25, printed pp.955–960, particularly
p.960 (PDF p.977); B.4.2 and B.4.5, printed pp.86–87.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels
open Representation Representation.BinaryOffender Subgroup BinaryPermutation
open StrongSections StrongSections.SourceConstituents
open OrthogonalQuotient.B4Extraction
open FourStructure.ChiefFactors FourStructure.CriticalTransfer Orthogonal.SourceTransport
open scoped commutatorElement IsMulCommutative

private theorem full_commutator
    {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
    {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    (s : ConjugationSection H UH Z ρ) (K : Subgroup G) (hK : K ≤ H)
    (hfull : ⁅UH, K⁆ = UH) :
    subspaceCommutator ρ ⊤ (Source.starImage H K) = ⊤ := by
  let C := subspaceCommutator ρ ⊤ (Source.starImage H K)
  have hc : ⁅K, UH⁆ ≤ preimage s C := by
    apply commutator_le.mpr
    intro k hk u hu
    let kH : H := ⟨k, hK hk⟩
    let uU : UH := ⟨u, hu⟩
    apply (mem_preimage s C ⟨⁅k,u⁆, s.commutator_mem kH uU⟩).mpr
    rw [← s.displacement kH uU]
    exact Submodule.subset_span
      ⟨_, mem_map_of_mem _ hk, _, Submodule.mem_top, rfl⟩
  have hu : UH ≤ preimage s C := by rwa [commutator_comm, hfull] at hc
  apply top_unique
  intro v _
  obtain ⟨u, huq⟩ := s.surjective (Multiplicative.ofAdd v)
  have hv := (mem_preimage s C u).mp (hu u.property)
  rw [huq] at hv
  exact hv


universe v
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- A local exclusion refers only to strong best offenders contained in A. -/
def HasStrongBestOffender (ρ : Representation (ZMod 2) H U) (A : Subgroup H) : Prop :=
  ∃ B ≤ A, IsBestOffender ρ B ∧ IsStrongOffender ρ B

/-- The transvection output on the actual sections, in one permutation marking. -/
structure TransvectionModels (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (K A : Subgroup H) (eH : H ≃* Perm) where
  actor_marking : A.map eH.toMonoidHom = transpositionGroup
  component_marking : K.map eH.toMonoidHom = alternatingGroup (Fin 8)
  quotient_natural : IsEightNatural W.quotientRepresentation eH
  J : Subrepresentation W.toRepresentation
  component_commutator : J.toSubmodule = subspaceCommutator W.toRepresentation ⊤ K
  model : IsEightNaturalOrCover J.toRepresentation eH
  rank_one : rank A = 1
  submodule_fixedCodim : fixedCodim W.toRepresentation A = 1
  quotient_fixedCodim : fixedCodim W.quotientRepresentation A = 1
  ambient_fixedCodim : fixedCodim ρ A = 2
  fixedSpace_lifts : (fixedSpace ρ A).map W.toSubmodule.mkQ =
    fixedSpace W.quotientRepresentation A

/-- Source alternatives after recognition. The first two alternatives retain
strong offenders and literal commutator models; the third retains both possible
positions of the critical line, as well as the marked transvection sections.
This is an output specification, never an input to recognition. -/
def SourceModelAlternatives
    {G : Type v} [Group G] [Finite G] (H V₃ V₁ K Uγ A₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (s : ConjugationSection H (Source.UH H V₃) V₁ τ)
    (W : Subrepresentation τ) (eH : Source.Hstar H ≃* Perm) : Prop :=
  (HasStrongBestOffender W.quotientRepresentation (Source.starImage H Uγ) ∧
    ∃ g : Perm,
      Nonempty (MarkedModels τ W (Source.starImage H K) (Source.starImage H Uγ)
        (conjugateMarking eH g)) ∧
      fixedCodim W.toRepresentation (Source.starImage H Uγ) ≤ 5) ∨
  (¬ HasStrongBestOffender W.quotientRepresentation (Source.starImage H Uγ)) ∧
    ((¬ A₁ ≤ preimage s W.toSubmodule ∧
      HasStrongBestOffender W.toRepresentation (Source.starImage H Uγ) ∧
      ∃ g : Perm,
        Nonempty (MarkedModels τ W (Source.starImage H K) (Source.starImage H Uγ)
          (conjugateMarking eH g)) ∧
        fixedCodim W.toRepresentation (Source.starImage H Uγ) = 3) ∨
    (¬ HasStrongBestOffender W.toRepresentation (Source.starImage H Uγ)) ∧
      A₁ ≤ Source.UH H V₃ ∧ IsAtom (s.image A₁) ∧
      ⁅Source.DH (Source.UH H V₃) Uγ A₁, Uγ⁆ = A₁ ∧
      ((A₁ ≤ preimage s W.toSubmodule ∧
          W.toSubmodule ≤ s.image (Source.DH (Source.UH H V₃) Uγ A₁) ∧
          subspaceCommutator τ W.toSubmodule (Source.starImage H Uγ) = s.image A₁) ∨
        (¬ A₁ ≤ preimage s W.toSubmodule ∧
          W.toSubmodule ⊔ s.image (Source.DH (Source.UH H V₃) Uγ A₁) = ⊤ ∧
          subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H Uγ) =
            (s.image A₁).map W.toSubmodule.mkQ)) ∧
      ∃ g : Perm,
        Nonempty (TransvectionModels τ W (Source.starImage H K) (Source.starImage H Uγ)
          (conjugateMarking eH g)))

/-- All offender branches on the chosen actual source section. The source
13.8.21(4) group equality supplies full linear commutator generation and,
together with the marked component, faithfulness of both sections. The
critical-pair index and displacement data supply the complete local sieve.
Only the universal earlier B.4 classifications are external representation
inputs: no constituent, extension, actor marking or rank is assumed. -/
theorem source_offender_model_alternatives
    {G : Type v} [Group G] [Finite G] (H V₃ V₁ K Uγ A₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (s : ConjugationSection H (Source.UH H V₃) V₁ τ)
    (W : Subrepresentation τ) (hW : IsCoatom W)
    (eH : Source.Hstar H ≃* Perm)
    (hK : (Source.starImage H K).map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hKW : ∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule,
      W.toRepresentation k w ≠ w)
    (hKH : K ≤ H) (hfull : ⁅Source.UH H V₃, K⁆ = Source.UH H V₃)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic τ (Source.starImage H Uγ))
    (hb : fixedCodim τ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ))
    (hUγ : Uγ ≤ H) (hn : Source.UH H V₃ ≤ normalizer (A₁ : Set G))
    (hA₁ : Nat.card A₁ = 2)
    (hindex : Nat.log 2 ((Source.DH (Source.UH H V₃) Uγ A₁).relIndex (Source.UH H V₃)) ≤
      rank (Source.starImage H Uγ))
    (hS : SymmetricB4.{v} (Source.starImage H K) eH)
    (hC : ∀ eK : Source.starImage H K ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace,
      ComponentB4.{v} (Source.starImage H K) eH eK) :
    SourceModelAlternatives H V₃ V₁ K Uγ A₁ τ s W eH := by
  classical
  have hgen := full_commutator s K hKH hfull
  have hproper : W.toSubmodule ≠ ⊤ := fun he =>
    hW.ne_top (Subrepresentation.toSubmodule_injective he)
  obtain ⟨hfaithW, hfaithQ⟩ := faithful_source_sections s K hKH hfull W hproper
    (marked_component_monolith eH _ hK) hKW
  have hnoncentral : ¬ (⊤ : Submodule (ZMod 2) W.toSubmodule) ≤
      fixedSpace W.toRepresentation (Source.starImage H K) := by
    intro hfix
    obtain ⟨k, hk, w, hw⟩ := hKW
    exact hw (hfix Submodule.mem_top ⟨k, hk⟩)
  unfold SourceModelAlternatives
  by_cases hsQ : HasStrongBestOffender W.quotientRepresentation (Source.starImage H Uγ)
  · left
    refine ⟨hsQ, ?_⟩
    have hs : ∃ B ≤ Source.starImage H Uγ, IsStrongOffender W.quotientRepresentation B := by
      obtain ⟨B, hBA, _, hB⟩ := hsQ
      exact ⟨B, hBA, hB⟩
    obtain ⟨⟨c⟩, _⟩ := strong_quotient_series τ W eH _ hK hQ hnoncentral
      _ hA hq hb hs hS
    obtain ⟨g, hg, hKg, hQg, _, _, hw, _⟩ :=
      strong_quotient_constituent_multiplicity τ W eH _ hK hQ c _ hA hb hs
    exact ⟨g, marked_models_of_series τ W (conjugateMarking eH g) _ _ hKg hg hQg hgen
      (c.conjugate W.toRepresentation _ eH g) hw, hw⟩
  · refine Or.inr ⟨hsQ, ?_⟩
    by_cases hsW : HasStrongBestOffender W.toRepresentation (Source.starImage H Uγ)
    · left
      let eK : Source.starImage H K ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace :=
        ((eH.subgroupMap _).trans (MulEquiv.subgroupCongr hK)).trans
          BinaryNaturalDual.FourActors.linearAlternatingEquiv.symm
      have hs : ∃ B ≤ Source.starImage H Uγ, IsStrongOffender W.toRepresentation B := by
        obtain ⟨B, hBA, _, hB⟩ := hsW
        exact ⟨B, hBA, hB⟩
      obtain ⟨c⟩ := strong_submodule_series τ W eH _ hK eK hnoncentral _ hq hs hS (hC eK)
      obtain ⟨g, hg, hKg, hQg, hr, hcodW, _⟩ :=
        strong_submodule_constituent_multiplicity τ W eH _ hK hQ c _ hA hs
      obtain ⟨m⟩ := marked_models_of_series τ W (conjugateMarking eH g) _ _ hKg hg hQg
        hgen (c.conjugate W.toRepresentation _ eH g) (by omega)
      refine ⟨?_, hsW, g, ⟨m⟩, hcodW⟩
      intro hle
      have hlineW : s.image A₁ ≤ W.toSubmodule := by
        rw [← image_preimage s W.toSubmodule]
        exact s.image_mono hle
      obtain ⟨hdim, _, hdisp⟩ := critical_linear_data s Uγ A₁ hUγ hn hA₁ hindex
      obtain ⟨_, _, hs | ⟨_, _, heq, _⟩⟩ := quotient_offender_sieve τ W _ hA
        (fun a ha d hd => hlineW (hdisp a ha d hd)) hdim
      · exact hsQ hs
      · have := m.quotient_fixedCodim
        omega
    · right
      obtain ⟨hle, hatom, hcomm, hposition, hr, hw, hq', hu, hfix, g, J,
          hg, hKg, hQg, hJ, hmodel⟩ :=
        TransvectionSections.source_compatible_sections H V₃ V₁ K Uγ A₁ τ s W hW eH hK hQ
          hfaithW hfaithQ hKW hA hq hb hUγ hn hA₁ hindex hsW hsQ
      exact ⟨hsW, hle, hatom, hcomm, hposition, g, ⟨{
        actor_marking := hg
        component_marking := hKg
        quotient_natural := hQg
        J := J
        component_commutator := hJ
        model := hmodel
        rank_one := hr
        submodule_fixedCodim := hw
        quotient_fixedCodim := hq'
        ambient_fixedCodim := hu
        fixedSpace_lifts := hfix }⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels
