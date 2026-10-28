module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.Model
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.FivePoint.Symmetric
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Ambient
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Construction

/-!
# The five-point endpoint of K.3.1.2

A comparison of the Hermitian model with the five-point augmentation core
gives the marked A₅ action on the original layer. Normality and faithfulness
then put the whole ambient action in S₅. A proper overgroup of the marked A₅
is S₅, with the same coordinates. The symmetric branch has ratio one,
the precise commuting-transposition best-offender family, and its offenders
generate the original ambient group.

The constructed comparison identifies the Hermitian action through its five
nonzero singular vectors and preserves the chosen minus form. The source
application discharges this comparison input, retaining the conditional API
as well. The independent inner-actor calculation supplies the A₅ minima to
the orthogonal assembly; this module completes the action identification and
the S₅ offender branch.

Source: Aschbacher–Smith, K.3.1.2, B.3.2(4), B.4.2(5), and B.4.5,
printed pp.454, 84, 86–87.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender BinaryPermutation
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.FivePoint
open ChapterB.QuasisimpleSource ChapterB.Offenders

local instance fivePointFixedAlgebra : Algebra (ZMod 2) (fixedField 1) := ZMod.algebra _ 2
local instance fivePointBinarySpace : Module (ZMod 2) (Space 1) :=
  Module.compHom (Space 1) (algebraMap (ZMod 2) (fixedField 1))

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

namespace OrthogonalModel
variable (M : OrthogonalModel 1 ρ L) (C : Comparison)

/-- The actual five-point coordinates on the original module. -/
def fivePointCoordinates : V ≃ₗ[ZMod 2] core (Fin 5) := M.coordinates.trans C.coordinates

/-- The same coordinates in the source's natural quotient module. -/
def fivePointNaturalCoordinates : V ≃ₗ[ZMod 2] natural (Fin 5) :=
  (M.fivePointCoordinates C).trans (coreEquivNatural (Fin 5) (by decide))

theorem fivePoint_intertwines (g : L) (v : V) :
    M.fivePointCoordinates C (ρ g.val v) =
      coreRepresentation (Fin 5) (C.groupEquiv (M.groupEquiv g)).val
        (M.fivePointCoordinates C v) := by
  change C.coordinates (M.coordinates (ρ g.val v)) = _
  rw [M.intertwines, C.intertwines]
  rfl

theorem fivePoint_natural_intertwines (g : L) (v : V) :
    M.fivePointNaturalCoordinates C (ρ g.val v) =
      naturalRepresentation (Fin 5) (C.groupEquiv (M.groupEquiv g)).val
        (M.fivePointNaturalCoordinates C v) := by
  change coreEquivNatural (Fin 5) (by decide) (M.fivePointCoordinates C (ρ g.val v)) = _
  rw [M.fivePoint_intertwines C, coreEquivNatural_equivariant]
  rfl

/-- Compatibility is with the already fixed minus coordinates, not merely
with an unspecified form of the same dimension. -/
theorem fivePoint_minus_form (v : V) :
    ClassicalOrthogonal.Minus.quadraticForm (fixedField 1) 2 (M.minusCoordinates v) =
      algebraMap (ZMod 2) (fixedField 1)
        (BinaryPermutation.FiveGeometry.form (M.fivePointCoordinates C v)) :=
  C.minus_form (M.coordinates v)

/-- The marked layer acts on the actual five-point core, with no remaining
comparison premise. These are Hermitian, rather than natural SL₂(4), coordinates. -/
def fivePointCoreAction : ActionEquiv (ρ.comp L.subtype)
    ((coreRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype) where
  groupEquiv := M.groupEquiv.trans Construction.comparison.groupEquiv
  linearEquiv := M.fivePointCoordinates Construction.comparison
  intertwines := M.fivePoint_intertwines Construction.comparison

/-- The constructed action comparison preserves the already specified minus
quadratic form on the original representation. -/
theorem fivePointCoreAction_minus_form (v : V) :
    ClassicalOrthogonal.Minus.quadraticForm (fixedField 1) 2 (M.minusCoordinates v) =
      algebraMap (ZMod 2) (fixedField 1)
        (BinaryPermutation.FiveGeometry.form (M.fivePointCoreAction.linearEquiv v)) :=
  M.fivePoint_minus_form Construction.comparison v

end OrthogonalModel

variable [Finite G]

/-- The actual A₅/S₅ alternatives and all S₅ clauses of B.4.2(5), once the
Hermitian/five-point comparison is constructed. No ratio or offender
classification is assumed in either source hypothesis or model. -/
theorem SourceHypotheses.fivePoint_alternatives_of_comparison
    (h : SourceHypotheses ρ L) (M : OrthogonalModel 1 ρ L) (C : Comparison) :
    (L = ⊤ ∧ Nonempty (ActionEquiv ρ
      ((naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype))) ∨
    ∃ e : ActionEquiv ρ (naturalRepresentation (Fin 5)),
      L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin 5) ∧
      quadraticRatio ρ = 1 ∧ offenderSubgroup ρ = ⊤ ∧
      (∀ A : Subgroup G, IsBestOffender ρ A ↔
        CaseAFamily 5 (A.map e.groupEquiv.toMonoidHom)) ∧
      ∀ A : Subgroup G, IsBestOffender ρ A →
        A = Subgroup.closure {a | a ∈ A ∧ (e.groupEquiv a).IsSwap} ∧
          ∀ a ∈ A, ∀ b ∈ A, Commute a b := by
  let : L.Normal := h.layer_normal
  by_cases hL : L = ⊤
  · refine Or.inl ⟨hL, ?_⟩
    subst L
    exact ⟨{
      groupEquiv := Subgroup.topEquiv.symm.trans (M.groupEquiv.trans C.groupEquiv)
      linearEquiv := M.fivePointNaturalCoordinates C
      intertwines := fun g v => M.fivePoint_natural_intertwines C ⟨g, Subgroup.mem_top g⟩ v }⟩
  · obtain ⟨f, hf, hi, hm⟩ := exists_ambient_permutation ρ L
      (M.groupEquiv.trans C.groupEquiv) (M.fivePointNaturalCoordinates C)
      (M.fivePoint_natural_intertwines C) h.faithful
    have hmap : L.map f = alternatingGroup (Fin 5) := by
      ext p
      constructor
      · rintro ⟨l, hl, rfl⟩
        rw [hm ⟨l, hl⟩]
        exact (C.groupEquiv (M.groupEquiv ⟨l, hl⟩)).property
      · intro hp
        obtain ⟨l, hl⟩ := (M.groupEquiv.trans C.groupEquiv).surjective ⟨p, hp⟩
        exact ⟨l, l.property, (hm l).trans (congrArg Subtype.val hl)⟩
    have hs : Function.Surjective f := surjective_of_marked_alternating L f hf hmap hL
    let e : ActionEquiv ρ (naturalRepresentation (Fin 5)) := {
      groupEquiv := MulEquiv.ofBijective f ⟨hf, hs⟩
      linearEquiv := M.fivePointNaturalCoordinates C
      intertwines := hi }
    exact Or.inr ⟨e, hmap, FivePoint.symmetric_conclusion e⟩

/-- The `s = 1` action alternatives of K.3.1.2, including the entire S₅
offender conclusion of B.4.2(5), on the original group and representation.
The Hermitian/five-point comparison is constructed, not an extra hypothesis.
The A₅ minima are supplied separately by the inner-actor calculation. -/
theorem SourceHypotheses.fivePoint_alternatives
    (h : SourceHypotheses ρ L) (M : OrthogonalModel 1 ρ L) :
    (L = ⊤ ∧ Nonempty (ActionEquiv ρ
      ((naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype))) ∨
    ∃ e : ActionEquiv ρ (naturalRepresentation (Fin 5)),
      L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin 5) ∧
      quadraticRatio ρ = 1 ∧ offenderSubgroup ρ = ⊤ ∧
      (∀ A : Subgroup G, IsBestOffender ρ A ↔
        CaseAFamily 5 (A.map e.groupEquiv.toMonoidHom)) ∧
      ∀ A : Subgroup G, IsBestOffender ρ A →
        A = Subgroup.closure {a | a ∈ A ∧ (e.groupEquiv a).IsSwap} ∧
          ∀ a ∈ A, ∀ b ∈ A, Commute a b :=
  h.fivePoint_alternatives_of_comparison M Construction.comparison

end CFSG.Quasithin.ChapterK.RankOne
