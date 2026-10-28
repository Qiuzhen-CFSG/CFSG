module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Assembly
-- Intentional internal reuse of the central splitting proof: its hypotheses
-- are only Irr+, faithfulness, irreducibility and the actual cyclic center.
-- In particular it does not assume the legacy tripleSix offender clause.
import all CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.ExtensionClauses

/-!
# The corrected projective-line catalogue on the chosen module

The current B.5 theorem uses the vector-plane convention in the triple-six
row. All other constructors have identical action data. We reuse their
comparisons, and prove the triple-six comparison directly from its center,
quotient marking and dimension. Its central extension splits by the
central-element cohomology proof; no legacy offender clause is constructed.
Source: Aschbacher--Smith B.4.2(8), B.5.1 and 12.2.2, pp.86,99--103,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.ExtensionConsequences
open ChapterB PerfectCentralCovering
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H] [Finite H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)
include c

/-- Concrete hexacode coordinates for the actual corrected triple cover. -/
theorem corrected_tripleSix_marking
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (s : MovedSection ρ K) (a : SourceInduction.ProjectiveLine.TripleSixAction s.action K) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms,
      (∀ q, Atlas.Codes.hexEvenCoordinate (e q) =
        a.quotientEquiv (QuotientGroup.mk' (center K) (c.projection q))) ∧
      Function.Injective c.projection := by
  let := hq
  let := c.nontrivial
  let : IsQuasisimple K := IsQuasisimple.of_surjective c.projection c.surjective
  let f := a.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hk : f.ker = center K :=
    (MonoidHom.ker_comp_of_injective _ _ a.quotientEquiv.injective).trans (QuotientGroup.ker_mk' _)
  have hcard : Nat.card f.ker = 3 := by
    rw [hk,Nat.card_congr a.centerEquiv.toEquiv]
    simp
  obtain ⟨j,hj⟩ := Hexacode.triple_cover_equiv f
    (a.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le hcard
  let p := j.toMonoidHom.comp c.projection
  have hp : Function.Injective p := Hexacode.injective_of_surjective_of_twoCore_eq_bot
    (pCore_quotient_pCore_eq_bot 2) p (j.surjective.comp c.surjective)
  refine ⟨MulEquiv.ofBijective p ⟨hp,j.surjective.comp c.surjective⟩,?_,?_⟩
  · intro q
    exact DFunLike.congr_fun hj (c.projection q)
  · intro x y he
    exact hp (congrArg j he)

/-- The corrected triple-six row gives the original faithful six-dimensional
irreducible module with its concrete covering-group marking. -/
theorem corrected_tripleSix
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (s : MovedSection ρ K)
    (hi : IsIrrPlus ρ K s.space.toSubmodule)
    (hf : Function.Injective s.action)
    (hirr : IsIrreducible (s.action.comp K.subtype))
    (a : SourceInduction.ProjectiveLine.TripleSixAction s.action K) :
    ModuleAlternatives1222 D := by
  obtain ⟨e,_,hp⟩ := c.corrected_tripleSix_marking hq s a
  have hs := SourceCompletion.central_isCompl s hi hf hirr a.centerEquiv
  let b := c.wholeCentralMarking s hs hp
  refine .tripleSix e (b.linearEquiv.finrank_eq.trans a.dimension) ?_
    (irreducible_of_equiv b hirr)
  intro q r he
  apply hp
  apply c.faithful
  change ρ (c.projection q) = ρ (c.projection r)
  rw [c.action,c.action,he]

omit c [Finite H] in
/-- Only the triple-six constructor changes in the corrected catalogue.
No conversion is asserted for its incompatible offender convention. -/
theorem corrected_catalogue_or_triple {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) H W} {J : Subgroup H}
    (hc : SourceInduction.ProjectiveLine.IrreducibleActionCase σ K J) :
    IrreducibleActionCase σ K J ∨
      Nonempty (SourceInduction.ProjectiveLine.TripleSixAction σ K) := by
  cases hc with
  | linearTwo F hg e ho hq => exact Or.inl (.linearTwo F hg e ho hq)
  | linearThree F hg e hq => exact Or.inl (.linearThree F hg e hq)
  | symplectic F hd hg e hq => exact Or.inl (.symplectic F hd hg e hq)
  | symplecticTwo e hq => exact Or.inl (.symplecticTwo e hq)
  | g2 F hd hg e ho hq => exact Or.inl (.g2 F hd hg e ho hq)
  | g2Two e ho hq => exact Or.inl (.g2Two e ho hq)
  | symmetric n hn e ho hq => exact Or.inl (.symmetric n hn e ho hq)
  | alternatingSix hg e ho hq => exact Or.inl (.alternatingSix hg e ho hq)
  | alternatingSeven hg hw e hd ho hq => exact Or.inl (.alternatingSeven hg hw e hd ho hq)
  | tripleSix _ a _ => exact Or.inr ⟨a⟩
  | binaryLinear d hd hg e hq => exact Or.inl (.binaryLinear d hd hg e hq)
  | orthogonalSix hg hw e ho hq => exact Or.inl (.orthogonalSix hg hw e ho hq)
  | symmetricEight hw e hq => exact Or.inl (.symmetricEight hw e hq)
  | exteriorFive hg hw e hd ho hq => exact Or.inl (.exteriorFive hg hw e hd ho hq)

/-- Compare every constructor of the actual corrected B.5.1 conclusion. -/
theorem alternatives_of_corrected_source_exits_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False)
    (b : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K) :
    ModuleAlternatives1222 D := by
  cases b.clause_one with
  | irreducible hi hf hirr hs he =>
    rcases corrected_catalogue_or_triple hs with hs | ha
    · exact c.alternatives_of_irreducible_source_exits_of_many
        h hmany horbits hff hrank hnonbinary b.sectionData ⟨hi,hf,hirr,hs,he⟩
    · exact c.corrected_tripleSix h.quasisimple b.sectionData hi hf hirr (Classical.choice ha)
  | doubleThree F _ e _ _ => exact (c.not_doubleThree b.sectionData F e).elim
  | naturalDual d hd _ he =>
    obtain ⟨e⟩ := he
    exact (c.not_naturalDual b.sectionData (by omega) e).elim
  | repeatedNatural d r hd hr _ _ he =>
    obtain ⟨e⟩ := he
    exact c.repeatedNatural h.quasisimple b.sectionData hd hr e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
