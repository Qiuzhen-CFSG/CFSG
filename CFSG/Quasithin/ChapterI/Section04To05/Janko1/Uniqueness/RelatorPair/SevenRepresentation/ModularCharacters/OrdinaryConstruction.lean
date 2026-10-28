module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.Arithmetic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.Source
public import Theory.Character.InnerProductByClasses
public import Theory.Character.AlternatingSix.Rational.NormOne
public import Theory.Character.DegreeCompleteness

/-!
# Constructing the ordinary table from its two substantive calculations

The literal table has norm-one distinct rows and positive degrees. Once its
rows are differences of genuine representation characters on the actual
classes, the generalized-character norm-one theorem realizes each row as
an irreducible representation. The sum of squared degrees equals the given
group order, so no further irreducible character can be missing.

`ordinaryDataOfGeneralizedRows` performs this construction, including the
compatible column relabeling, and returns precisely `OrdinaryData G`.
`ordinaryData_of_source` discharges both inputs from the source involution
centralizer data, simplicity, supplied group order and involution fusion.
The class enumeration uses local centralizers and class-size exhaustion;
the generalized rows use compatible power labels, cyclic restriction
calculations and Brauer's nilpotent restriction criterion. No recognition or
modular representation is assumed.

Source: Janko, J. Algebra 3 (1966), 147–186, ordinary-character calculation;
Gorenstein, *Finite Groups*, §16.6, printed p.482. See
`ModularCharacters/Source.md` for the numerical conventions and provenance.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

variable {G : Type*} [Group G] [Finite G] {c : OrdinaryClassData G}

/-- Interpret a numerical row on the actual, compatibly labeled classes. -/
@[expose] public def OrdinaryGeneralizedRows.character (r : OrdinaryGeneralizedRows c)
    (i : Fin 15) : ConjClassFunction G :=
  fun d => ordinaryValue r.rootFive r.rootNineteen i (r.labels.symm (c.classes.symm d))

/-- Evaluation uses the chosen labeling without changing the table. -/
public theorem OrdinaryGeneralizedRows.character_value (r : OrdinaryGeneralizedRows c)
    (i j : Fin 15) : r.character i (c.classes (r.labels j)) =
      ordinaryValue r.rootFive r.rootNineteen i j := by
  simp [character]

/-- The actual identity has the prescribed ordinary degree. -/
public theorem OrdinaryGeneralizedRows.character_degree (r : OrdinaryGeneralizedRows c)
    (i : Fin 15) : r.character i (ConjClasses.mk 1) = (ordinaryDegree i : ℂ) := by
  have hz : c.classes (r.labels 0) = ConjClasses.mk 1 := by
    rw [r.labels_zero, c.classes_eq, c.identity]
  rw [← hz, r.character_value, ordinaryValue_identity]

/-- Class sizes turn the numerical norm calculation into the group inner product. -/
public theorem OrdinaryGeneralizedRows.character_norm (r : OrdinaryGeneralizedRows c)
    (i : Fin 15) : classFunctionInner (r.character i) (r.character i) = 1 := by
  have hr : Function.Bijective (fun j => ConjClasses.mk (c.representatives (r.labels j))) := by
    simpa only [← c.classes_eq, Function.comp_def] using
      c.classes.bijective.comp r.labels.bijective
  rw [classFunctionInner_eq_sum_div_centralizer
    (fun j => c.representatives (r.labels j)) hr]
  simp_rw [← c.classes_eq, r.character_value, c.centralizers, r.labels_centralizers]
  exact ordinaryValue_norm r.rootFive_primitive r.rootNineteen_primitive i

/-- Generalized-character realization and positive degree give a genuine irreducible. -/
public theorem OrdinaryGeneralizedRows.character_irreducible (r : OrdinaryGeneralizedRows c)
    (i : Fin 15) : IsIrreducibleConjCharacter (r.character i) := by
  have hp : 0 < (r.character i (ConjClasses.mk 1)).re := by
    rw [r.character_degree, Complex.natCast_re]
    exact_mod_cast ordinaryDegree_pos i
  obtain ⟨n, ρ, _, heq⟩ := (r.generalized i).irreducible_of_norm_one (r.character_norm i) hp
  refine ⟨⟨n, ρ, ?_⟩, r.character_norm i⟩
  ext d
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep d
  exact congrFun heq g

/-- Every ordinary row gives a different character of the source group. -/
public theorem OrdinaryGeneralizedRows.character_injective (r : OrdinaryGeneralizedRows c) :
    Function.Injective r.character := by
  intro i j hij
  apply ordinaryValue_injective r.rootFive_primitive r.rootNineteen_primitive
  funext k
  simpa only [r.character_value] using congrFun hij (c.classes (r.labels k))

/-- The supplied group order and degree-square sum leave no omitted irreducibles. -/
public theorem OrdinaryGeneralizedRows.character_complete (r : OrdinaryGeneralizedRows c)
    (horder : Nat.card G = 175560) : IsCompleteIrreducibleCharacterFamily r.character := by
  apply completeIrreducibleFamily_of_sum_degree_normSq _ r.character_irreducible r.character_injective
  simp_rw [r.character_degree]
  rw [horder]
  exact ordinaryDegree_normSq_sum

/-- Assemble actual irreducibles from generalized rows on the actual classes.
The generalized-character input, unlike numerical orthogonality, supplies
representation realization; the degree-square sum supplies completeness. -/
public def ordinaryDataOfGeneralizedRows (c : OrdinaryClassData G)
    (r : OrdinaryGeneralizedRows c) (horder : Nat.card G = 175560) : OrdinaryData G where
  representatives j := c.representatives (r.labels j)
  classes := r.labels.trans c.classes
  classes_eq j := c.classes_eq (r.labels j)
  identity := by rw [r.labels_zero, c.identity]
  orders j := (c.orders (r.labels j)).trans (r.labels_orders j)
  centralizers j := (c.centralizers (r.labels j)).trans (r.labels_centralizers j)
  chi := r.character
  complete := r.character_complete horder
  rootFive := r.rootFive
  rootFive_primitive := r.rootFive_primitive
  rootNineteen := r.rootNineteen
  rootNineteen_primitive := r.rootNineteen_primitive
  values := r.character_value

/-- The exact shared ordinary-table contract, conditional on the two source calculations. -/
public theorem ordinaryData_of_generalizedRows (c : OrdinaryClassData G)
    (r : OrdinaryGeneralizedRows c) (horder : Nat.card G = 175560) :
    Nonempty (OrdinaryData G) :=
  ⟨ordinaryDataOfGeneralizedRows c r horder⟩

/-- The complete literal ordinary character table of the arbitrary source group.
The actual class census and generalized-character realizations are constructed
from the source hypotheses, then norm one and the degree-square sum establish
irreducibility and completeness. No additional character or labeling input remains. -/
public theorem ordinaryData_of_source [IsSimpleGroup G]
    (h : CFSG.Quasithin.Janko1CentralizerData G)
    (horder : Nat.card G = 175560)
    (hfusion : ∀ x : G, orderOf x = 2 → ∃ g : G, g * x * g⁻¹ = h.z) :
    Nonempty (OrdinaryData G) := by
  obtain ⟨c⟩ := nonempty_ordinaryClassData_of_order h horder hfusion
  obtain ⟨r⟩ := ordinaryGeneralizedRows_of_source h horder hfusion c
  exact ordinaryData_of_generalizedRows c r horder

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
