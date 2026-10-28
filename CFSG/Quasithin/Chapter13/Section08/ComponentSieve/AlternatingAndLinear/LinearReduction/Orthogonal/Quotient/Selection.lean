module

public import Theory.Representation.SubrepresentationLattice
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.Order.Atoms.Finite

/-!
# The literal maximal quotient in the orthogonal branch

Choose a maximal proper invariant subspace of U_H/V₁. Its quotient is
irreducible, and the image of the generating two-space V₃/V₁ is still a
two-space. Both the parabolic action and commutator generation descend along
the actual quotient map. The final theorem uses the conjugation action on
Source.Utilde; it does not replace that module by an abstract vector space.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.25, printed pp.959–960, PDF pp.976–977.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
open Representation Representation.BinaryOffender
open FourStructure FourStructure.ChiefFactors

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

private theorem irreducible_quotient (W : Subrepresentation ρ) (hW : IsCoatom W) :
    W.quotientRepresentation.IsIrreducible := by
  have hn : W.toSubmodule ≠ ⊤ := fun he => hW.1 (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial (U ⧸ W.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hn
  refine ⟨?_⟩
  intro S
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.comap W.toSubmodule.mkQ
    apply_mem_toSubmodule g v hv := S.apply_mem_toSubmodule g hv }
  have hWT : W ≤ T := by
    intro v hv
    change W.toSubmodule.mkQ v ∈ S
    have hz : W.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact S.toSubmodule.zero_mem
  rcases eq_or_lt_of_le hWT with he | hlt
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro w hw
    obtain ⟨v, rfl⟩ := W.toSubmodule.mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).mpr (show v ∈ W from he.symm ▸ hw)
  · right
    have ht : T = ⊤ := hW.2 T hlt
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    obtain ⟨v, rfl⟩ := W.toSubmodule.mkQ_surjective w
    exact (show v ∈ T from ht.symm ▸ (show v ∈ (⊤ : Subrepresentation ρ) from by trivial))

/-- The image carries the restriction of the literal quotient action. -/
def quotientSeed (s : GeneratingSeed ρ) (W : Subrepresentation ρ) :
    Subrepresentation (W.quotientRepresentation.comp s.parabolic.subtype) where
  toSubmodule := s.space.toSubmodule.map W.toSubmodule.mkQ
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, s.space.apply_mem_toSubmodule g hv, rfl⟩

/-- A generating irreducible two-space injects into every proper quotient. -/
theorem quotientSeed_finrank (s : GeneratingSeed ρ) (W : Subrepresentation ρ)
    (hW : W ≠ ⊤) :
    Module.finrank (ZMod 2) (quotientSeed ρ s W).toSubmodule = 2 := by
  let f := W.toSubmodule.mkQ.comp s.space.toSubmodule.subtype
  have hr : LinearMap.range f = (quotientSeed ρ s W).toSubmodule := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  rw [← hr, LinearMap.finrank_range_of_inj (s.quotient_injective ρ W hW), s.dim_two]

private theorem commutator_map_quotient (W : Subrepresentation ρ)
    (S : Submodule (ZMod 2) U) (L : Subgroup H) :
    subspaceCommutator W.quotientRepresentation (S.map W.toSubmodule.mkQ) L =
      (subspaceCommutator ρ S L).map W.toSubmodule.mkQ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨ρ g v - v, Submodule.subset_span ⟨g, hg, v, hv, rfl⟩, map_sub _ _ _⟩
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    change W.toSubmodule.mkQ (ρ g v - v) ∈ (subspaceCommutator W.quotientRepresentation (S.map W.toSubmodule.mkQ) L)
    rw [map_sub]
    exact Submodule.subset_span ⟨g, hg, W.toSubmodule.mkQ v,
      Submodule.mem_map_of_mem hv, rfl⟩

/-- The source equality V̂₃ = [V̂₃,L₁] descends without changing the actor. -/
theorem quotientSeed_commutator (s : GeneratingSeed ρ) (W : Subrepresentation ρ)
    (L : Subgroup H) (hL : subspaceCommutator ρ s.space.toSubmodule L = s.space.toSubmodule) :
    subspaceCommutator W.quotientRepresentation (quotientSeed ρ s W).toSubmodule L =
      (quotientSeed ρ s W).toSubmodule := by
  change subspaceCommutator W.quotientRepresentation
    (s.space.toSubmodule.map W.toSubmodule.mkQ) L = _
  rw [commutator_map_quotient, hL]
  rfl

/-- Maximality and irreducibility are proved for the chosen literal quotient. -/
theorem exists_maximal_quotient [FiniteDimensional (ZMod 2) U]
    (s : GeneratingSeed ρ) :
    ∃ W : Subrepresentation ρ, IsCoatom W ∧ W.quotientRepresentation.IsIrreducible ∧
      Module.finrank (ZMod 2) (quotientSeed ρ s W).toSubmodule = 2 := by
  classical
  let : Finite U := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun W : Subrepresentation ρ => (W : Set U)) SetLike.coe_injective
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro he
    have ht : (⊤ : Submodule (ZMod 2) U) = ⊥ :=
      (congrArg Subrepresentation.toSubmodule he).symm
    have hs : s.space.toSubmodule = ⊥ := le_bot_iff.mp (ht ▸ le_top)
    have hd := s.dim_two
    rw [hs, finrank_bot] at hd
    omega
  obtain ⟨W, hW, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  exact ⟨W, hW, irreducible_quotient ρ W hW, quotientSeed_finrank ρ s W hW.1⟩

open scoped IsMulCommutative

/-- The actual V₃ image in a selected irreducible quotient of U_H/V₁,
with the source parabolic invariance and commutator equality retained. -/
theorem exists_source_maximal_quotient
    {G : Type*} [Group G] [Finite G] (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hτ : IsSourceAction H V₃ V₁ τ)
    (P T L₁ : Subgroup (Source.Hstar H)) (hTP : T ≤ P) (hT : IsPGroup 2 T)
    (hstable : ∀ g : P, ∀ v ∈ sourceSeedSpace H V₃ V₁, τ g v ∈ sourceSeedSpace H V₃ V₁)
    (hirr : IsAtom (⟨sourceSeedSpace H V₃ V₁, hstable⟩ : Subrepresentation (τ.comp P.subtype)))
    (hdim : Module.finrank (ZMod 2) (sourceSeedSpace H V₃ V₁) = 2)
    (hcomm : subspaceCommutator τ (sourceSeedSpace H V₃ V₁) L₁ = sourceSeedSpace H V₃ V₁) :
    ∃ W : Subrepresentation τ, IsCoatom W ∧ W.quotientRepresentation.IsIrreducible ∧
      Module.finrank (ZMod 2) ((sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ) = 2 ∧
      (∀ g : P, ∀ v ∈ (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ,
        W.quotientRepresentation g v ∈ (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ) ∧
      subspaceCommutator W.quotientRepresentation
        ((sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ) L₁ =
        (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ := by
  let s := sourceSeed H V₃ V₁ τ hτ P T hTP hT hstable hirr hdim
  obtain ⟨W, hW, hi, hd⟩ := exists_maximal_quotient τ s
  exact ⟨W, hW, hi, hd, (quotientSeed τ s W).apply_mem_toSubmodule,
    quotientSeed_commutator τ s W L₁ hcomm⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
