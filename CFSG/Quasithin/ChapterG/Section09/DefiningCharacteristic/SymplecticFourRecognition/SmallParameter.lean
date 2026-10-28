module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.ComponentBounds
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter.NaturalComparison
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter.FlagModule

public import Theory.Representation.Quotient

/-!
# The smallest derived symplectic parameter in G.9.3(9)

The genuine component hypotheses bound the original module by eight.
Transport along the given equivalence to Sp₄(F)′, and then along its polar
identification with A₆, retains faithfulness and irreducibility. An
order-five element gives the independent lower bound four.

G.5.1 supplies the intended remaining representation input: over F₂ the
irreducibles have degrees 1, 4, 4 and 16, and the two degree-four actions
are the two automorphic natural actions. Once this universal catalogue
is proved, the extreme degrees are excluded and `NaturalComparison`
constructs the required group and linear equivalences. The catalogue is
an explicit premise below; this module does not yet prove G.9.3(9).

The separate flag-filtration route isolates two finite calculations:
a composition series over F₂ with degrees 1, 4 and 16, and recognition
of the degree-four actions. Neither is inferred from dimension. In
particular, the two degree-eight factors over F₄ cannot be substituted
for binary irreducibles. Every conditional assembly retains the original
ambient group, representation, actor, rank and SQTK-cover hypotheses.
No K-group classification theorem is invoked with a partial class.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.5.1, printed pp.342--343, and G.9.3(9), printed pp.354,356--357.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter

open Representation BinaryPermutation Theory.SpecificGroups.SymmetricSix

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}
  {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
/-- A faithful action of the actual derived carrier has degree at least four. -/
theorem binary_component_finrank_ge_four
    (h : ComponentHypothesis K ρ A L L m) (hF : Nat.card F = 2)
    (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) F)) :
    4 ≤ Module.finrank (ZMod 2) V := by
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hF)
  exact degree_ge_four ((ρ.comp L.subtype).comp a.symm.toMonoidHom)
    ((h.faithful.comp L.subtype_injective).comp a.symm.injective)

omit [Algebra (ZMod 2) F] in
/-- A proved binary flag filtration forces degree four in the source window. -/
theorem binary_component_finrank_eq_four_of_flag_filtration
    (h : ComponentHypothesis K ρ A L L m) (hF : Nat.card F = 2)
    (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) F))
    (hfiltration : FactorDegreeFiltration
      {d : ℕ | d = 1 ∨ d = 4 ∨ d = 16} flagRepresentation) :
    Module.finrank (ZMod 2) V = 4 := by
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hF)
  let σ := (ρ.comp L.subtype).comp a.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff
      a.symm.toMonoidHom a.symm.surjective (ρ.comp L.subtype)).mpr h.irreducible
  exact degree_eq_four_of_filtration hfiltration σ
    ((h.faithful.comp L.subtype_injective).comp a.symm.injective)
    (binary_component_bounds h hF e).2

/-- Conditional assembly from the concrete binary filtration and the universal
four-dimensional recognition theorem. Both extra inputs remain to be proved. -/
theorem binary_component_recognition_of_flag_filtration
    (h : ComponentHypothesis K ρ A L L m) (hF : Nat.card F = 2)
    (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) F))
    (hfiltration : FactorDegreeFiltration
      {d : ℕ | d = 1 ∨ d = 4 ∨ d = 16} flagRepresentation)
    (hfour : ∀ σ : Representation (ZMod 2) A6 V,
      σ.IsIrreducible → Function.Injective σ → Module.finrank (ZMod 2) V = 4 →
        Quasiequivalent σ (alternatingNaturalRepresentation (Fin 6))) :
    Quasiequivalent (ρ.comp L.subtype) (binaryNatural F) := by
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hF)
  let σ := (ρ.comp L.subtype).comp a.symm.toMonoidHom
  have hi : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff
      a.symm.toMonoidHom a.symm.surjective (ρ.comp L.subtype)).mpr h.irreducible
  have hf : Function.Injective σ :=
    (h.faithful.comp L.subtype_injective).comp a.symm.injective
  have hd := binary_component_finrank_eq_four_of_flag_filtration h hF e hfiltration
  obtain ⟨b, f, hf⟩ := hfour σ hi hf hd
  apply quasiequivalent_binaryNatural_of_alternatingNatural hF
  refine ⟨a.trans b, f, ?_⟩
  intro g v
  have hh := hf (a g) v
  change f (ρ (a.symm (a g)) v) =
    alternatingNaturalRepresentation (Fin 6) (b (a g)) (f v) at hh
  simpa only [MulEquiv.symm_apply_apply, MulEquiv.trans_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using hh
/-- G.5.1 implies the smallest-parameter recognition branch once its full
binary catalogue and natural-module identifications have been supplied. -/
theorem binary_component_recognition_of_alternating_catalogue
    (h : ComponentHypothesis K ρ A L L m) (hF : Nat.card F = 2)
    (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) F))
    (hcatalogue : ∀ σ : Representation (ZMod 2) A6 V,
      σ.IsIrreducible → Module.finrank (ZMod 2) V = 1 ∨
        Quasiequivalent σ (alternatingNaturalRepresentation (Fin 6)) ∨
        Module.finrank (ZMod 2) V = 16) :
    Quasiequivalent (ρ.comp L.subtype) (binaryNatural F) := by
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hF)
  let σ := (ρ.comp L.subtype).comp a.symm.toMonoidHom
  have hi : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff
      a.symm.toMonoidHom a.symm.surjective (ρ.comp L.subtype)).mpr h.irreducible
  have hf : Function.Injective σ :=
    (h.faithful.comp L.subtype_injective).comp a.symm.injective
  have hq : Quasiequivalent σ (alternatingNaturalRepresentation (Fin 6)) := by
    rcases hcatalogue σ hi with hd | hq | hd
    · have := degree_ge_four σ hf
      omega
    · exact hq
    · have := (binary_component_bounds h hF e).2
      omega
  obtain ⟨b, f, hf⟩ := hq
  apply quasiequivalent_binaryNatural_of_alternatingNatural hF
  refine ⟨a.trans b, f, ?_⟩
  intro g v
  have hh := hf (a g) v
  change f (ρ (a.symm (a g)) v) =
    alternatingNaturalRepresentation (Fin 6) (b (a g)) (f v) at hh
  simpa only [MulEquiv.symm_apply_apply, MulEquiv.trans_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using hh

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter
