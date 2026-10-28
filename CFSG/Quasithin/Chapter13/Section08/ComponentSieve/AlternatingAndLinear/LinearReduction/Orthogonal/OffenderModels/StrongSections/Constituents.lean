module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.Marking
public import Theory.Representation.BinaryOffender.FlagCodimension
public import Theory.Representation.BinaryOffender.QuadraticDisjointSummands
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Natural constituents in the two strong-offender branches

A series here consists of literal invariant subspaces with central or marked
natural successive quotients. It specifies an intermediate output of the
constituent classification, not an additional source hypothesis.

Once the actor is the disjoint-transposition group, every natural factor
contributes three to fixed codimension. The bound five therefore permits at
most one natural factor, even in nonsplit extensions. A strong offender on
the submodule descends to any natural constituent; this identifies the whole
actor and makes its fixed codimension on the submodule exactly three.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.25,
printed p.960, PDF p.977 (1 March 2004 manuscript). Constructing the classified
series from the earlier source setup, and recognizing its commutator extension,
are separate obligations. Neither is asserted by this module.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections
open Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- A finite invariant series, with a nonempty collection of natural factors.
Centrality is tested against the actual component K. No splitting, chief-factor
uniqueness or indecomposability is included. -/
structure NaturalCentralSeries (ρ : Representation (ZMod 2) H U)
    (K : Subgroup H) (eH : H ≃* Perm) where
  length : ℕ
  space : ℕ → Subrepresentation ρ
  monotone : Monotone space
  first : space 0 = ⊥
  last : space length = ⊤
  factors : ∀ i < length,
    (∀ k ∈ K, ∀ v, sectionRepresentation ρ (space i) (space (i + 1)) k v = v) ∨
    IsEightNatural (sectionRepresentation ρ (space i) (space (i + 1))) eH
  natural_exists : ∃ i < length,
    IsEightNatural (sectionRepresentation ρ (space i) (space (i + 1))) eH

/-- Perfectness follows from the compatible alternating-component marking. -/
theorem perfect_component_of_marking (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) : Group.IsPerfect K := by
  let e : K ≃* alternatingGroup (Fin 8) :=
    (K.equivMapOfInjective eH.toMonoidHom eH.injective).trans (MulEquiv.subgroupCongr hK)
  let : Group.IsPerfect (alternatingGroup (Fin 8)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- Nontriviality of the component action constructs the occurrence of a
natural factor. It need not be supplied separately by constituent recognition. -/
noncomputable def NaturalCentralSeries.of_nontrivial
    (ρ : Representation (ZMod 2) H U) (K : Subgroup H) (eH : H ≃* Perm)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hnontrivial : ¬ (⊤ : Submodule (ZMod 2) U) ≤ fixedSpace ρ K)
    (n : ℕ) (c : ℕ → Subrepresentation ρ) (hc : Monotone c)
    (hfirst : c 0 = ⊥) (hlast : c n = ⊤)
    (hfactors : ∀ i < n,
      (∀ k ∈ K, ∀ v, sectionRepresentation ρ (c i) (c (i + 1)) k v = v) ∨
      IsEightNatural (sectionRepresentation ρ (c i) (c (i + 1))) eH) :
    NaturalCentralSeries ρ K eH where
  length := n
  space := c
  monotone := hc
  first := hfirst
  last := hlast
  factors := hfactors
  natural_exists := by
    classical
    let : Group.IsPerfect K := perfect_component_of_marking eH K hK
    by_contra h
    apply hnontrivial
    have hcentral : ∀ i < n, ∀ k ∈ K, ∀ v,
        sectionRepresentation ρ (c i) (c (i + 1)) k v = v := by
      intro i hi
      rcases hfactors i hi with hfix | hnatural
      · exact hfix
      · exact (h ⟨i, hi, hnatural⟩).elim
    have hfix := le_fixedSpace_of_central_flag ρ K c hfirst n hcentral
    rw [hlast] at hfix
    exact hfix

/-- Change only the permutation coordinates; the actual series is unchanged. -/
def NaturalCentralSeries.conjugate (ρ : Representation (ZMod 2) H U)
    (K : Subgroup H) (eH : H ≃* Perm) (s : NaturalCentralSeries ρ K eH) (g : Perm) :
    NaturalCentralSeries ρ K (conjugateMarking eH g) where
  length := s.length
  space := s.space
  monotone := s.monotone
  first := s.first
  last := s.last
  factors i hi := (s.factors i hi).imp id (fun h => h.conjugate _ eH g)
  natural_exists := by
    obtain ⟨i, hi, h⟩ := s.natural_exists
    exact ⟨i, hi, h.conjugate _ eH g⟩

variable [FiniteDimensional (ZMod 2) U]

/-- Under the marked D action, the bound five proves uniqueness, rather than
assuming that the module has only one natural chief factor. -/
theorem natural_factor_unique (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8)
    (hbudget : fixedCodim ρ A ≤ 5)
    (c : ℕ → Subrepresentation ρ) (hc : Monotone c) (n : ℕ)
    {i j : ℕ} (hi : i < n) (hj : j < n)
    (hNi : IsEightNatural (sectionRepresentation ρ (c i) (c (i + 1))) eH)
    (hNj : IsEightNatural (sectionRepresentation ρ (c j) (c (j + 1))) eH) : i = j := by
  have hdi := fixedCodim_eightNaturalOrCover _ eH (Or.inl hNi) A hA
  have hdj := fixedCodim_eightNaturalOrCover _ eH (Or.inl hNj) A hA
  exact eq_of_flag_fixedCodim_bounds ρ c hc n 3 A (by omega) hi hj
    (by omega) (by omega)

/-- A classified series with the bound five has exactly one natural factor. -/
theorem NaturalCentralSeries.exists_unique_natural (ρ : Representation (ZMod 2) H U)
    (K : Subgroup H) (eH : H ≃* Perm) (s : NaturalCentralSeries ρ K eH)
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8)
    (hbudget : fixedCodim ρ A ≤ 5) :
    ∃! i : ℕ, i < s.length ∧
      IsEightNatural (sectionRepresentation ρ (s.space i) (s.space (i + 1))) eH := by
  obtain ⟨i, hi, hNi⟩ := s.natural_exists
  refine ⟨i, ⟨hi, hNi⟩, ?_⟩
  rintro j ⟨hj, hNj⟩
  exact natural_factor_unique ρ eH A hA hbudget s.space s.monotone s.length hj hi hNj hNi

/-- A strong offender on the whole module remains strong on every section.
This statement concerns the same subgroup, before taking a faithful image. -/
theorem strong_on_section (ρ : Representation (ZMod 2) H U)
    (L N : Subrepresentation ρ) (B : Subgroup H) (hB : IsStrongOffender ρ B) :
    IsStrongOffender (sectionRepresentation ρ L N) B :=
  ⟨hB.1, (fixedCodim_section_le ρ L N B).trans_lt hB.2⟩

/-- A single actual natural constituent suffices to mark the whole actor in
the strong-submodule branch. No model for the whole module is assumed. -/
theorem strong_constituent_actor_marking (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (L N : Subrepresentation ρ)
    (hN : IsEightNatural (sectionRepresentation ρ L N) eH)
    (A B : Subgroup H) (hA : IsElementaryTwo A) (hBA : B ≤ A)
    (hB : IsStrongOffender ρ B) :
    A = B ∧ ∃ g : Perm,
      A.map (conjugateMarking eH g).toMonoidHom = D 8 ∧
      IsEightNatural (sectionRepresentation ρ L N) (conjugateMarking eH g) ∧
      rank A = 4 ∧ fixedCodim ρ A = 3 := by
  obtain ⟨heq, g, hg, hNg⟩ := strong_natural_actor_marking _ eH hN A B hA hBA
    (strong_on_section ρ L N B hB)
  have hr : rank A = 4 := by
    rw [← rank_map_injective (conjugateMarking eH g).toMonoidHom
      (conjugateMarking eH g).injective A, hg]
    exact Eight.rank_D
  have hcost := fixedCodim_eightNaturalOrCover _ (conjugateMarking eH g)
    (Or.inl hNg) A hg
  have hlo := fixedCodim_section_le ρ L N A
  have hhi : fixedCodim ρ A < rank A := heq ▸ hB.2
  exact ⟨heq, g, hg, hNg, hr, by omega⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections
