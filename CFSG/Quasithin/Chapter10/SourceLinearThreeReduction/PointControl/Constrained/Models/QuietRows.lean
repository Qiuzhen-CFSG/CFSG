module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.QuietRecognition
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.NaturalDualExclusion
public import Theory.Representation.SL2.BinaryHermitianIrreducibility
public import Theory.Representation.Suzuki.NaturalIrreducibility
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.Representation.PSL3Two.FourNaturalRank

/-!
# Excluding the orthogonal and Suzuki source covers

The concrete Hermitian and Suzuki actions are irreducible over F₂.
Pullback along the literal original two-core quotient preserves that
irreducibility, so QuietRecognition prepares the original reduced orbit
and forces the original quotient to be SL₃(2). The Hermitian quotient is
binary SL₂ and the Suzuki quotient has three-free order, giving the two
contradictions without any additional preparation or fixedness premise.

Together with the proved natural and natural--dual exclusions, these
results leave only four identical natural copies among the marked
10.1.1 alternatives. The marking predicate asserts no exhaustion and does
not replace the additional normalizer clauses of that source lemma.
Row recognition and exclusion of the retained four-natural cover remain
with qt-d-10-nona5-point-constrained. Source applies the reduction to the
literal point-control contract while keeping these two obligations explicit.

Source: Aschbacher--Smith10.1.1(4),(7) and10.2.9, printed pp.741,751--752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The original Hermitian row is excluded with its literal quotient and
fixed kernel; neither preparation nor Thompson fixedness is assumed. -/
theorem Context.no_hermitian_cover (c : Context D t v I) (n : ℕ) [NeZero n]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field n)) :
    let : Algebra (ZMod 2) (fixedField n) := ZMod.algebra _ 2
    let : Module (ZMod 2) (Space n) :=
      Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))
    BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      ((SL2.BinarySmall.hermitian n).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) → False := by
  let : Algebra (ZMod 2) (fixedField n) := ZMod.algebra _ 2
  let : Module (ZMod 2) (Space n) :=
    Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : IsIrreducible ((SL2.BinarySmall.hermitian n).comp q) :=
    (irreducible_comp_surjective_iff q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) _).mpr
      (SL2.BinarySmall.hermitian_irreducible n)
  exact c.no_rankOne_irreducible_cover e

/-- The original Suzuki natural row is impossible on the literal moved
subgroup, with its entire fixed kernel and no extra preparation premise. -/
theorem Context.no_suzuki_natural_cover (c : Context D t v I)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      ((SuzukiNatural.natural m).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : IsIrreducible ((SuzukiNatural.natural m).comp q) :=
    (irreducible_comp_surjective_iff q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) _).mpr
      (SuzukiNatural.BinaryIrreducibility.natural_irreducible m hm)
  apply c.no_irreducible_cover_of_three_free _ s
  rw [Nat.card_congr e.toEquiv]
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm

/-- The original four-natural marking retained by this source owner.
No exhaustion or exclusion of this row is asserted by this definition. -/
@[expose] def FourNaturalCover
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
    Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.FourNatural.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

/-- Literal markings for the original source alternatives, retaining the
four-natural possibility. This is a predicate on coordinates, not a row
classification theorem. It records the group and module consequences used
here, without asserting the additional normalizer clauses of10.1.1.
The A₅ alternative retains its actual group isomorphism. -/
inductive OriginalMovedCover
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop
  | rankOne (h : Selection.RankOneNatural D)
  | alternatingFive (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  | naturalThree (h : Selection.BinaryThreeNatural D)
  | hermitian (n : ℕ) [NeZero n] (hn : 1 < n)
      (e : (L ⧸ pCore 2 L) ≃* SL(2,Field n))
      (s : letI : Algebra (ZMod 2) (fixedField n) := ZMod.algebra _ 2
        let : Module (ZMod 2) (Space n) :=
          Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))
        BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
          ((SL2.BinarySmall.hermitian n).comp
            (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
  | naturalDual (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
      (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
        (BinaryLinearThree.NaturalDual.action.comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
  | fourNatural (h : FourNaturalCover D)
  | suzuki (m : ℕ) (hm : 0 < m)
      (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
      (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
        ((SuzukiNatural.natural m).comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

/-- Every marked source alternative except four identical natural modules
is excluded on the original constrained context. Recognition of a marking
and exclusion of the retained row remain with this task's assembly owner. -/
theorem Context.four_natural_of_original_moved_cover (c : Context D t v I)
    (h : OriginalMovedCover D) : FourNaturalCover D := by
  cases h with
  | rankOne h => exact (c.no_rankOneNatural h).elim
  | alternatingFive e => exact (c.nonA5 ⟨e⟩).elim
  | naturalThree h => exact (c.no_binaryThreeNatural h).elim
  | hermitian n _ e s => exact (c.no_hermitian_cover n e s).elim
  | naturalDual e s => exact (c.no_naturalDual_cover e s).elim
  | fourNatural h => exact h
  | suzuki m hm e s => exact (c.no_suzuki_natural_cover m hm e s).elim

end CFSG.Quasithin.Chapter10.PointControl.Constrained
