module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.BlockExtensions
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.Filtration
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.Coordinates

/-!
# The complete twelve-dimensional binary SL₃(4) module catalogue

Every binary representation of dimension twelve satisfying `z² + z + 1 = 0`
is equivalent to one of thirty-four explicit marked block models. The natural
and dual six-dimensional binary modules exhaust the irreducible constituents.
There is one split model in each homogeneous orientation, and a family indexed
by F₄ × F₄ in each mixed orientation. Precisely the zero mixed parameter splits
as an extension; the other parameters retain the nonsplit alternatives.
The list need not have distinct underlying representation isomorphism types.

An irreducible submodule has dimension six, and the actual quotient also has
dimension six and is irreducible. A vector-space complement supplies block
coordinates without assuming an invariant complement. The complete extension
calculation then gives the actual whole-module representation equivalence.
No irreducibility, semisimplicity or extra extension premise is assumed.
All models are faithful, so faithfulness need not be an input to `classify`.

The catalogue retains the global block formulas and re-exports their values on
the proved transvection generators, for testing extension to the full Mathieu
group. This is an intrinsic SL₃(4) classification supporting James (1973),
Lemma 8.3, cited in Aschbacher–Smith H.12.1(1), printed pp.393–394.
Identification of the Mathieu point stabilizer and exclusion of competing
local entries by the full group belong to the restriction-recognition consumer.
-/

@[expose] public noncomputable section
namespace Representation.SL3FourLocalCatalogue

/-- The explicit finite structural family, retaining the ordered constituents
and the two field parameters in either mixed orientation. -/
def CatalogueEntry := (a : Constituent) × (b : Constituent) × ExtensionClass.Parameter a b

instance catalogueEntryFintype : Fintype CatalogueEntry := inferInstanceAs (Fintype (Σ a b, ExtensionClass.Parameter a b))

/-- The family has thirty-four marked entries. Repetitions among underlying
representation isomorphism types are permitted. -/
theorem card_catalogueEntry : Fintype.card CatalogueEntry = 34 := by
  change Fintype.card (Σ a b, ExtensionClass.Parameter a b) = 34
  rw [Fintype.card_sigma]
  simp only [Fintype.card_sigma, ExtensionClass.card_parameter]
  decide

/-- The explicit whole-module action attached to a structural entry. -/
def catalogueRepresentation (i : CatalogueEntry) : Representation (ZMod 2) SL (W × W) :=
  (ExtensionClass.model i.1 i.2.1 i.2.2).representation

theorem catalogueRepresentation_faithful (i : CatalogueEntry) :
    Function.Injective (catalogueRepresentation i) :=
  ExtensionClass.model_faithful i.1 i.2.1 i.2.2

theorem catalogueRepresentation_centralQuadratic (i : CatalogueEntry) :
    CentralQuadratic (catalogueRepresentation i) :=
  ExtensionClass.model_centralQuadratic i.1 i.2.1 i.2.2

/-- All group actions, including their extension blocks, remain explicit. -/
theorem catalogueRepresentation_apply (i : CatalogueEntry) (g : SL) (v : W × W) :
    catalogueRepresentation i g v =
      (constituent i.1 g v.1 + (ExtensionClass.model i.1 i.2.1 i.2.2).value g v.2,
        constituent i.2.1 g v.2) := rfl

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (σ : Representation (ZMod 2) SL U)

/-- Every twelve-dimensional binary module satisfying the central polynomial
belongs to the finite structural family by an actual representation equivalence.
No irreducibility or semisimplicity is assumed; faithfulness is automatic. -/
theorem classify (hq : CentralQuadratic σ) (hd : Module.finrank (ZMod 2) U = 12) :
    ∃ i : CatalogueEntry, Nonempty (σ.Equiv (catalogueRepresentation i)) := by
  obtain ⟨N, a, b, ⟨ea⟩, ⟨eb⟩⟩ := exists_constituent_filtration σ hq hd
  obtain ⟨c, ⟨e⟩⟩ := exists_block_equiv σ N ea eb
  have hc : c.IsCentral := c.centralQuadratic_iff.mp (centralQuadratic_of_equiv σ hq _ e)
  obtain ⟨r, ⟨f⟩⟩ := ExtensionClass.exists_model_equiv c hc
  exact ⟨⟨a, b, r⟩, ⟨e.trans f⟩⟩

/-- The structural catalogue describes exactly the requested modules. -/
theorem exists_catalogue_equiv_iff :
    (∃ i : CatalogueEntry, Nonempty (σ.Equiv (catalogueRepresentation i))) ↔
      CentralQuadratic σ ∧ Module.finrank (ZMod 2) U = 12 := by
  constructor
  · rintro ⟨i, ⟨e⟩⟩
    exact ⟨centralQuadratic_of_equiv _ (catalogueRepresentation_centralQuadratic i) σ e.symm,
      e.toLinearEquiv.finrank_eq.trans split_finrank⟩
  · rintro ⟨hq, hd⟩
    exact classify σ hq hd

end Representation.SL3FourLocalCatalogue
