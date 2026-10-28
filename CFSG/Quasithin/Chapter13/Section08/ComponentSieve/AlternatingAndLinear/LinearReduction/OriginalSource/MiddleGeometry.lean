module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.FixedSpace
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.Seed
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource

/-!
# Original critical geometry in the orthogonal middle-node exclusion

The selected source pair supplies the critical denominator, its rank bound,
and the larger endpoint actor. In the rank-one branch, faithfulness on both
sections forces fixed codimension two. The denominator has codimension at
most one, so its nonzero displacement makes the actual critical-line image
an atom. Equality in the F.9 bound identifies the full fixed space with the
literal group centralizer. The source centralizer commutator therefore gives
the displacement used by the orthogonal pointwise-centralizer contradiction.

The source application eliminates both strong-offender alternatives and the
remaining rank-one alternative. It retains the chosen natural quotient and
the two B.4 classification inputs; their construction in the marked middle
node belongs to qt-d-138-linear-source. No critical index or centralizer
callback is assumed.

Source: Aschbacher–Smith 13.8.22–25, printed pp.957–960/PDF pp.974–977.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
open TransvectionRecognition.Component.ModelExtension
open FourStructure.ChiefFactors FourStructure.CriticalTransfer
open Orthogonal.SourceTransport OrthogonalQuotient.B4Extraction OffenderModels
open SourceCompletion CriticalGeometry
open FieldComponents.HigherFieldReduction.ExternalModules
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]

omit [(V₁.subgroupOf (Source.UH H V₃)).Normal] in
private theorem rank_one_exclusion
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (w : CriticalInputs.SelectedWitness L T H V (sourceOne L T V₁) V₃ V₁ ρ)
    (W : Subrepresentation ρ)
    (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation)
    (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8))
    (t : TransvectionModels ρ W (Source.starImage H K)
      (Source.starImage H (w.pair.Ugamma V₃)) eH) : False := by
  let c := w.pair
  have hUV : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono d.seed_le le_rfl)
  have hUgH := hUV.trans w.actor_le
  have hgeom := local_earlierGeometry d hF9 c
  have hn : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) :=
    ((conjugateSpanBy_mono d.seed_le le_rfl).trans hgeom.VH_endpoint).trans
      (SectionActions.CriticalPair.normalizes_Aone c V₁
        (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
  have hcard : Nat.card (c.Aone V₁) = 2 := by
    rw [show c.Aone V₁ = V₁.map (MulAut.conj (c.gb : G)).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj (c.gb : G)).injective, d.line_card]
  have hsmall : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤ 2 := by
    have hh := w.quadratic_member.2.2
    rw [t.rank_one] at hh
    exact hh
  obtain ⟨_, _, htwo⟩ := faithful_sections_of_fixedCodim_le_two ρ W hW hQ
    w.quadratic_member.1.1 hsmall
  change fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) = 2 at htwo
  have hD := (critical_linear_data s (c.Ugamma V₃) (c.Aone V₁)
    hUgH hn hcard w.comparison).1
  have hnonfixed : ¬ s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)) ≤
      fixedSpace ρ (Source.starImage H (c.Ugamma V₃)) := by
    intro hle
    have hm := Submodule.finrank_mono hle
    have hd := (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁))).finrank_quotient_add_finrank
    have hf := fixedCodim_add_finrank ρ (Source.starImage H (c.Ugamma V₃))
    have hr := t.rank_one
    change rank (Source.starImage H (c.Ugamma V₃)) = 1 at hr
    omega
  have hline := (critical_commutator_of_nonfixed s (c.Ugamma V₃) (c.Aone V₁)
    hUgH hn hcard hnonfixed).2.2.1
  have hlt : Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma := by
    apply lt_of_le_of_ne (map_mono (comap_mono hUV))
    intro he
    change Source.starImage H (c.Ugamma V₃) = Source.starImage H c.Vgamma at he
    have hv : 1 < rank (Source.starImage H c.Vgamma) := w.rank_gt_one
    rw [← he] at hv
    have hr : rank (Source.starImage H (c.Ugamma V₃)) = 1 := t.rank_one
    omega
  apply rank_one_orthogonal_contradiction ρ W t.J eH t.model
    (Or.inl t.quotient_natural) hW hQ
    (Source.starImage H (c.Ugamma V₃)) (Source.starImage H c.Vgamma)
    w.quadratic_member.1.1 hlt t.actor_marking hsmall (s.image (c.Aone V₁)) hline
  exact Seven.OriginalSource.source_fixedSpace_displacement d hH hF9 c s w.comparison
    (by rw [htwo, t.rank_one])

/-- Apply the original critical geometry to all three orthogonal offender
branches. The literal maximal quotient and the B.4 inputs remain for the
middle-node representation argument; all source critical-line and larger-actor
premises of the terminal contradiction are constructed here. -/
theorem orthogonal_quotient_exclusion_source
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hN : (K.subgroupOf H).Normal) (hLK : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (w : CriticalInputs.SelectedWitness L T H V (sourceOne L T V₁) V₃ V₁ ρ)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8))
    (hKalt : (Source.starImage H K).map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : OffenderModels.IsEightNatural W.quotientRepresentation eH)
    (hKW : ∃ k ∈ Source.starImage H K, ∃ v : W.toSubmodule,
      W.toRepresentation k v ≠ v)
    (hS : SymmetricB4.{u} (Source.starImage H K) eH)
    (hC : ∀ eK : Source.starImage H K ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace,
      ComponentB4.{u} (Source.starImage H K) eH eK) : False := by
  let c := w.pair
  let s := CriticalInputs.sourceSection H V₃ V₁ ρ hρ hF9.plus_le_H
    (d.line_le_plane.trans d.plane_le_seed) hF9.H_centralizes
  have hUV : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono d.seed_le le_rfl)
  have hUgH := hUV.trans w.actor_le
  have hgeom := local_earlierGeometry d hF9 c
  have hn : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) :=
    ((conjugateSpanBy_mono d.seed_le le_rfl).trans hgeom.VH_endpoint).trans
      (SectionActions.CriticalPair.normalizes_Aone c V₁
        (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
  have hcard : Nat.card (c.Aone V₁) = 2 := by
    rw [show c.Aone V₁ = V₁.map (MulAut.conj (c.gb : G)).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj (c.gb : G)).injective, d.line_card]
  have hfull := Seven.OriginalSource.source_generated_original d hKH hN hLK
  have hproper : W.toSubmodule ≠ ⊤ := fun he =>
    hW.1 (Subrepresentation.toSubmodule_injective he)
  obtain ⟨hWfaith, hQfaith⟩ := faithful_source_sections s K hKH hfull.symm W hproper
    (marked_component_monolith eH (Source.starImage H K) hKalt) hKW
  have halt := source_offender_model_alternatives H V₃ V₁ K
    (c.Ugamma V₃) (c.Aone V₁) ρ s W hW eH hKalt hQ hKW hKH hfull.symm
    w.quadratic_member.1 w.quadratic_member.2.1 w.quadratic_member.2.2
    hUgH hn hcard w.comparison hS hC
  obtain ⟨hD, hdim, hdisp⟩ := critical_linear_data s (c.Ugamma V₃) (c.Aone V₁)
    hUgH hn hcard w.comparison
  rcases halt with hstrongQ | ⟨_, hrest⟩
  · obtain ⟨_, g, ⟨m⟩, _⟩ := hstrongQ
    exact orthogonal_sections_critical_line_contradiction ρ W m.J
      (conjugateMarking eH g) m.model (Or.inl m.quotient_natural)
      (Source.starImage H (c.Ugamma V₃)) m.actor_marking
      (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)))
      (s.image (c.Aone V₁)) hD hdim hdisp
  · rcases hrest with hstrongW | hrank
    · obtain ⟨_, _, g, ⟨m⟩, _⟩ := hstrongW
      exact orthogonal_sections_critical_line_contradiction ρ W m.J
        (conjugateMarking eH g) m.model (Or.inl m.quotient_natural)
        (Source.starImage H (c.Ugamma V₃)) m.actor_marking
        (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)))
        (s.image (c.Aone V₁)) hD hdim hdisp
    · obtain ⟨_, _, _, _, _, g, ⟨t⟩⟩ := hrank
      exact rank_one_exclusion d hH hF9 ρ s w W hWfaith hQfaith (conjugateMarking eH g) t

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
