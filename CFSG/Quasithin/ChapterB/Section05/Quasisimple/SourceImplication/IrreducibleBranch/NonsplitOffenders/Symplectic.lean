module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders.CoverReduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders.Symplectic.Transport
public import Theory.Representation.SymplecticNaturalNormalizer.Centralizers
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent

/-!
# Symplectic cover offenders lie in the component

The literal quotient of the local moved space cannot increase fixed
codimension. Its faithful action therefore transports any offender to the
natural binary symplectic normalizer. The semilinear fixed-space calculation,
including its equality case, proves containment using the bound of twice the
field degree for the two-rank of every outer-involution centralizer.

The final two theorems discharge this bound by the native-centralizer
calculation and symplectic field-cocycle descent, completing the containment
needed in the last symplectic case of B.5.1. The conditional reductions remain
available separately. The proof uses the source normality, faithful quotient
and actual natural-action equivalence; it makes no assertion that the covering
kernel is fixed by all of the local group.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.5.1,
printed p.100, with the covering convention I.1.5, p.408 and I.2.3, p.413.
The natural-quotient argument is an alternative to describing the orthogonal
cover explicitly. It does not require the ratio or nonzero-kernel hypotheses.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open SymplecticConjugatePair.Ambient.Normalizer
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- An offender on the literal local moved space descends to its quotient. -/
theorem local_moved_offender_descends [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) (D : Subgroup G) {A : Subgroup D}
    (hA : IsOffender (s.space.toRepresentation.comp D.subtype) A) :
    IsOffender (s.action.comp D.subtype) A := by
  let Z : Subrepresentation (s.space.toRepresentation.comp D.subtype) := {
    toSubmodule := s.central.toSubmodule
    apply_mem_toSubmodule g := s.central.apply_mem_toSubmodule g.val }
  have hb := fixedCodim_quotient_add_subrepresentation_le
    (s.space.toRepresentation.comp D.subtype) Z A
  have hq : fixedCodim (s.action.comp D.subtype) A ≤
      fixedCodim (s.space.toRepresentation.comp D.subtype) A := by
    change fixedCodim (s.action.comp D.subtype) A + _ ≤ _ at hb
    omega
  exact ⟨hA.1, hq.trans hA.2⟩

/-- The actual local cover consumer, conditional only on the stated native
outer-centralizer bound. No fixed-kernel assertion for all of LT is used. -/
theorem symplectic_local_bestOffender_le_of_centralizer_bound
    [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    (F : BinaryField) (hn : 1 < F.degree)
    (e : ActionEquiv (s.action.comp L.subtype) (binarySymplectic F))
    (hbound : ∀ a : naturalNormalizer (F := F.Carrier), orderOf a = 2 →
      a.val ∉ naturalDerivedImage →
      primeRank 2 (centralizer ({a} : Set (naturalNormalizer (F := F.Carrier)))) ≤
        2 * F.degree)
    {A : Subgroup ↥(L ⊔ (T : Subgroup G))}
    (hA : IsBestOffender
      (s.space.toRepresentation.comp (L ⊔ (T : Subgroup G)).subtype) A) :
    A ≤ L.subgroupOf (L ⊔ (T : Subgroup G)) := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let D := L ⊔ (T : Subgroup G)
  let L0 := L.subgroupOf D
  let σ := s.action.comp D.subtype
  let e0 : ActionEquiv (σ.comp L0.subtype) (binarySymplectic F) := {
    groupEquiv := (subgroupOfEquivOfLe (show L ≤ D from le_sup_left)).trans e.groupEquiv
    linearEquiv := e.linearEquiv
    intertwines := fun g v => e.intertwines ⟨g.val, g.property⟩ v }
  exact Symplectic.offender_le_natural_component_of_centralizer_bound σ
    (local_faithful h s T T.isPGroup') L0 F hn e0 hbound
    (local_moved_offender_descends s D (hA.isOffender _))

/-- The original Sylow-subgroup formulation required by the B.5.1 parent. -/
theorem symplectic_cover_bestOffender_le_of_centralizer_bound
    [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    (F : BinaryField) (hn : 1 < F.degree)
    (e : ActionEquiv (s.action.comp L.subtype) (binarySymplectic F))
    (hbound : ∀ a : naturalNormalizer (F := F.Carrier), orderOf a = 2 →
      a.val ∉ naturalDerivedImage →
      primeRank 2 (centralizer ({a} : Set (naturalNormalizer (F := F.Carrier)))) ≤
        2 * F.degree)
    (A : Subgroup G) (hAT : A ≤ T)
    (hA : IsBestOffender
      (s.space.toRepresentation.comp (L ⊔ (T : Subgroup G)).subtype)
      (A.subgroupOf (L ⊔ (T : Subgroup G)))) : A ≤ L := by
  have hle := symplectic_local_bestOffender_le_of_centralizer_bound h s T F hn e hbound hA
  have hAD : A ≤ L ⊔ (T : Subgroup G) := hAT.trans le_sup_right
  intro a ha
  exact hle (show (⟨a, hAD ha⟩ : ↥(L ⊔ (T : Subgroup G))) ∈
    A.subgroupOf (L ⊔ (T : Subgroup G)) from ha)

/-- Every best offender on the local moved cover lies in the symplectic component.
The native centralizer bound is discharged by genuine symplectic field descent. -/
theorem symplectic_local_bestOffender_le
    [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    (F : BinaryField) (hn : 1 < F.degree)
    (e : ActionEquiv (s.action.comp L.subtype) (binarySymplectic F))
    {A : Subgroup ↥(L ⊔ (T : Subgroup G))}
    (hA : IsBestOffender
      (s.space.toRepresentation.comp (L ⊔ (T : Subgroup G)).subtype) A) :
    A ≤ L.subgroupOf (L ⊔ (T : Subgroup G)) := by
  apply symplectic_local_bestOffender_le_of_centralizer_bound h s T F hn e ?_ hA
  exact SymplecticNaturalNormalizer.outer_centralizer_rank_le_of_descent F.card_eq hn
    (Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.half_frobenius_cocycle_coboundary
      F.card_eq hn)

/-- Symplectic cover-offender containment in the original Sylow-subgroup formulation
of B.5.1, with no additional centralizer or field-descent premise. -/
theorem symplectic_cover_bestOffender_le
    [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    (F : BinaryField) (hn : 1 < F.degree)
    (e : ActionEquiv (s.action.comp L.subtype) (binarySymplectic F))
    (A : Subgroup G) (hAT : A ≤ T)
    (hA : IsBestOffender
      (s.space.toRepresentation.comp (L ⊔ (T : Subgroup G)).subtype)
      (A.subgroupOf (L ⊔ (T : Subgroup G)))) : A ≤ L := by
  have hle := symplectic_local_bestOffender_le h s T F hn e hA
  have hAD : A ≤ L ⊔ (T : Subgroup G) := hAT.trans le_sup_right
  intro a ha
  exact hle (show (⟨a, hAD ha⟩ : ↥(L ⊔ (T : Subgroup G))) ∈
    A.subgroupOf (L ⊔ (T : Subgroup G)) from ha)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
