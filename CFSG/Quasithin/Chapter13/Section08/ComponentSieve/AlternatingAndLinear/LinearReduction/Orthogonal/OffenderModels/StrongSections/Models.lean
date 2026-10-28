module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Extensions
public import Theory.Representation.Quotient

/-!
# Marked commutator models for the strong branches

A natural constituent is irreducible on the actual alternating component.
The fixed-codimension budget permits exactly one such factor. The extension
lemmas then recognize the literal component commutator as the natural module
or its augmentation core. Ambient commutator generation identifies its image
with the whole-group commutator, retaining its inclusion in W and U.

The output uses one marking for the component, actor, natural quotient and
commutator model. Its two fixed-codimension calculations give the lower bound
six needed by the subsequent source argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.3.1(1), B.3.3 and 13.8.25, printed pp.83–84 and 960 (1 March 2004).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections
open Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- The marked natural module remains irreducible on the actual component,
not merely on the whole symmetric actor. -/
theorem eightNatural_component_irreducible
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hN : IsEightNatural ρ eH) : IsIrreducible (ρ.comp K.subtype) := by
  let eK : K ≃* alternatingGroup (Fin 8) :=
    (K.equivMapOfInjective eH.toMonoidHom eH.injective).trans (MulEquiv.subgroupCongr hK)
  let σ := (alternatingNaturalRepresentation (Fin 8)).comp eK.toMonoidHom
  have hσ : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eK.toMonoidHom eK.surjective _).mpr
      (alternatingNatural_isIrreducible (by decide))
  obtain ⟨e, he⟩ := hN
  let E : Representation.Equiv (ρ.comp K.subtype) σ := .mk e (fun k => by
    apply LinearMap.ext
    intro u
    change e (ρ k u) = naturalRepresentation (Fin 8) (eH k) (e u)
    exact he k u)
  let f := IntertwiningMap.equivLinearMapAsModule _ _ E.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.bijective)
  rw [irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mpr ((irreducible_iff_isSimpleModule_asModule σ).mp hσ)

private theorem submodule_commutator_map (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (K : Subgroup H) :
    (subspaceCommutator W.toRepresentation ⊤ K).map W.toSubmodule.subtype =
      subspaceCommutator ρ W.toSubmodule K := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, w, _, rfl⟩
    change ρ k (w : U) - (w : U) ∈ subspaceCommutator ρ W.toSubmodule K
    exact Submodule.subset_span ⟨k, hk, w, w.property, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, w, hw, rfl⟩
    refine ⟨W.toRepresentation k ⟨w, hw⟩ - ⟨w, hw⟩, ?_, rfl⟩
    exact Submodule.subset_span ⟨k, hk, ⟨w, hw⟩, Submodule.mem_top, rfl⟩

variable [FiniteDimensional (ZMod 2) U]

/-- Concrete outputs of recognition, all under the displayed single marking.
In particular J is the actual commutator inside W; its mapped image is [W,H]
in U. This is an output structure, not a source hypothesis. -/
structure MarkedModels (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (K A : Subgroup H) (eH : H ≃* Perm) where
  actor_marking : A.map eH.toMonoidHom = D 8
  component_marking : K.map eH.toMonoidHom = alternatingGroup (Fin 8)
  quotient_natural : IsEightNatural W.quotientRepresentation eH
  J : Subrepresentation W.toRepresentation
  component_commutator : J.toSubmodule = subspaceCommutator W.toRepresentation ⊤ K
  whole_commutator : J.toSubmodule.map W.toSubmodule.subtype =
    subspaceCommutator ρ W.toSubmodule ⊤
  model : IsEightNaturalOrCover J.toRepresentation eH
  rank_four : rank A = 4
  quotient_fixedCodim : fixedCodim W.quotientRepresentation A = 3
  commutator_fixedCodim : fixedCodim J.toRepresentation A = 3
  six_le_fixedCodim : 6 ≤ fixedCodim ρ A

/-- Recognition from a classified series and its proved fixed-codimension
budget. Uniqueness and component irreducibility are deductions, not inputs. -/
theorem marked_models_of_series
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* Perm) (K A : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hA : A.map eH.toMonoidHom = D 8)
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤)
    (s : NaturalCentralSeries W.toRepresentation K eH)
    (hbudget : fixedCodim W.toRepresentation A ≤ 5) :
    Nonempty (MarkedModels ρ W K A eH) := by
  obtain ⟨i, ⟨hi, hNi⟩, huniq⟩ :=
    s.exists_unique_natural W.toRepresentation K eH A hA hbudget
  obtain ⟨hwhole, J, hJ, hmodel⟩ :=
    Extensions.whole_commutator_extension_of_unique_natural ρ W eH K hK hQ hgen
      s i hi hNi (fun j hj hNj => huniq j ⟨hj, hNj⟩)
      (eightNatural_component_irreducible _ eH K hK hNi)
  refine ⟨{
    actor_marking := hA
    component_marking := hK
    quotient_natural := hQ
    J := J
    component_commutator := hJ
    whole_commutator := ?_
    model := hmodel
    rank_four := ?_
    quotient_fixedCodim := fixedCodim_eightNaturalOrCover _ eH (Or.inl hQ) A hA
    commutator_fixedCodim := fixedCodim_eightNaturalOrCover _ eH hmodel A hA
    six_le_fixedCodim := six_le_fixedCodim_of_orthogonal_sections ρ W J eH
      hmodel (Or.inl hQ) A hA }⟩
  · rw [hJ, submodule_commutator_map, hwhole]
  · rw [← rank_map_injective eH.toMonoidHom eH.injective A, hA]
    exact Eight.rank_D

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections
