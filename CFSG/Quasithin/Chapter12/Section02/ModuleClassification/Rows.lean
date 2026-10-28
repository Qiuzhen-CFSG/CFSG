module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CoverRecovery
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Branches
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FaithfulComparison
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.RowReduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.ThreeCover
public import Theory.Representation.FirstCohomologyDuality.Indecomposable

/-!
# The surviving binary rows on the original chosen module

The B.5 fixed quotient is compared with the literal chosen quotient.
Cohomology splitting restores the whole module in the exterior, triple-cover,
and binary linear rows. The natural three-space retains its possible
four-dimensional central extension. Alternating rows use L/C_L(V).
Source: Aschbacher--Smith B.5.1 and 12.2.2, pp.99--103,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.ExtensionConsequences
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H] [Finite H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)
include c

omit [Finite H] in
/-- Splitting in B.5 is fixed-freeness when its moved space is the actual choice. -/
theorem central_eq_bot_of_split (s : MovedSection ρ K)
    (hs : IsCompl s.space.toSubmodule (fixedSpace ρ K)) : s.central.toSubmodule = ⊥ := by
  have hz : fixedSpace ρ K = ⊥ := eq_bot_of_top_isCompl (c.space_eq_top s ▸ hs)
  rw [s.central_eq]
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact hz.le (fun k => congrArg Subtype.val (hv k))

@[expose] noncomputable def wholeCentralEquiv (s : MovedSection ρ K)
    (hs : IsCompl s.space.toSubmodule (fixedSpace ρ K)) :
    D.space ≃ₗ[ZMod 2] (s.space.toSubmodule ⧸ s.central.toSubmodule) :=
  (c.spaceEquiv s).symm.trans
    (s.central.toSubmodule.quotEquivOfEqBot (c.central_eq_bot_of_split s hs)).symm

noncomputable def wholeCentralMarking (s : MovedSection ρ K)
    (hs : IsCompl s.space.toSubmodule (fixedSpace ρ K))
    (hp : Function.Injective c.projection) :
    ActionEquiv D.quotientAction (s.action.comp K.subtype) where
  groupEquiv := MulEquiv.ofBijective c.projection ⟨hp,c.surjective⟩
  linearEquiv := c.wholeCentralEquiv s hs
  intertwines q v := by
    change Submodule.Quotient.mk ((c.spaceEquiv s).symm (D.quotientAction q v)) =
      Submodule.Quotient.mk (s.space.toRepresentation (c.projection q) ((c.spaceEquiv s).symm v))
    congr 1
    apply (c.spaceEquiv s).injective
    change D.quotientAction q v = ρ (c.projection q) v
    exact (LinearMap.congr_fun (c.action q) v).symm

omit [Finite H] in
/-- All natural alternating rows use the literal centralizer quotient,
without assuming the two-core quotient is simple or centerless. -/
theorem alternating (s : MovedSection ρ K) {n : ℕ} (hn : 5 ≤ n) (hn' : n ≤ 8)
    (e : ActionEquiv (s.action.comp K.subtype) (alternatingNatural n)) :
    ModuleAlternatives1222 D := by
  let := D.actionCentralizer_normal
  exact .alternating n hn hn' ((c.faithfulCentralMarking s).trans e)

/-- The nonsplit/split distinction does not change the printed alternating row. -/
theorem alternatingSevenFour (s : MovedSection ρ K)
    (hi : IrreducibleAlternative K s) (e : K ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) :
    ModuleAlternatives1222 D := by
  let := D.actionCentralizer_normal
  have hs := alternatingSeven_isCompl s hi e hd
  exact .alternatingSevenFour (c.faithfulEquiv.trans e)
    ((c.wholeCentralEquiv s hs).finrank_eq.trans hd)

omit [Finite H] in
/-- The natural binary three-space lifts either to itself or its four-dimensional
indecomposable extension on the original chosen space. -/
theorem linearThree (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (s : MovedSection ρ K) (hi : IsIrrPlus ρ K s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp K.subtype) (linearNatural BinaryField.two 3)) :
    ModuleAlternatives1222 D := by
  have hp := c.projection_injective_of_linearThree hq e.groupEquiv
  rcases ModuleClassification.natural_three_isomorphism_or_dimension_four s hi e with ha | hd
  · obtain ⟨a⟩ := ha
    exact .linear 3 (Or.inl rfl) ((c.wholeMarking s hp).trans a)
  · exact D.alternatives_of_linearThree_four
      ((MulEquiv.ofBijective c.projection ⟨hp,c.surjective⟩).trans e.groupEquiv)
      ((c.spaceEquiv s).finrank_eq.symm.trans hd)

/-- Binary degree-four/five natural rows lift from the fixed quotient to V
because their central extensions split. -/
theorem binaryLinear (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (s : MovedSection ρ K) (hi : IrreducibleAlternative K s)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : ActionEquiv (s.action.comp K.subtype) (linearNatural BinaryField.two d)) :
    ModuleAlternatives1222 D := by
  have hp := c.projection_injective_of_binaryLinear hq hd e.groupEquiv
  have hs := binaryLinear_isCompl s hi.irrPlus (by omega) e
  exact .linear d (Or.inr hd) ((c.wholeCentralMarking s hs hp).trans e)

omit [Finite H] in
/-- The repeated-natural B.5 row gives a single natural module on the
original L/O2(L), after multiplicity reduction and cover recovery. -/
theorem repeatedNatural (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (s : MovedSection ρ K) {d r : ℕ} (hd : d = 4 ∨ d = 5) (hr : 0 < r)
    (e : ActionEquiv (s.space.toRepresentation.comp K.subtype)
      (repeated (linearNatural BinaryField.two d) r)) : ModuleAlternatives1222 D := by
  obtain ⟨a⟩ := c.repeated_natural_single s hd hr e
  have hp := c.projection_injective_of_binaryLinear hq hd a.groupEquiv
  exact .linear d (Or.inr hd) ((c.wholeMarking s hp).trans a)

/-- The ten-dimensional exterior row keeps its original actor and lifts
irreducibility from the central quotient using the proved cohomology vanishing. -/
theorem exteriorFive (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (s : MovedSection ρ K) (hi : IrreducibleAlternative K s)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 10) :
    ModuleAlternatives1222 D := by
  have hp := c.projection_injective_of_binaryLinear hq (Or.inr rfl) e
  have hs := exteriorFive_isCompl s hi e hd
  let a := c.wholeCentralMarking s hs hp
  exact .linearFiveExterior (a.groupEquiv.trans e) (a.linearEquiv.finrank_eq.trans hd)
    (irreducible_of_equiv a hi.irreducible)

omit [Finite H] in
/-- The binary derived G2 row retains its literal commutator subgroup
and recovers the original two-core actor. -/
theorem derivedG2 (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (s : MovedSection ρ K)
    (e : ActionEquiv (s.action.comp K.subtype) (g2DerivedNatural (ZMod 2))) :
    ModuleAlternatives1222 D := by
  have hp := c.projection_injective_of_binaryDerivedG2 hq e.groupEquiv
  exact .g2 ((c.quotientMarking s hp).trans e)

/-- The actual B.4.2 triple-cover row gives source case (g), including the
original two-core actor, faithfulness and irreducibility on the whole V. -/
theorem tripleSix (hq : IsQuasisimple (L ⧸ pCore 2 L)) (s : MovedSection ρ K)
    (hi : IrreducibleAlternative K s) (a : TripleSixAction s.action K) :
    ModuleAlternatives1222 D := by
  obtain ⟨e,_,hp⟩ := c.tripleSix_marking hq s a
  have hs := tripleSix_isCompl s hi a
  let b := c.wholeCentralMarking s hs hp
  refine .tripleSix e (b.linearEquiv.finrank_eq.trans a.dimension) ?_
    (irreducible_of_equiv b hi.irreducible)
  intro q r he
  apply hp
  apply c.faithful
  change ρ (c.projection q) = ρ (c.projection r)
  rw [c.action,c.action,he]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
