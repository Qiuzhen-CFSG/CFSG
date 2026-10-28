module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceDefs
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty

/-!
# The degree-thirty gap for the actual simple M22 component

Pull back the faithful irreducible component action along the inverse of the
given isomorphism to the actual M22. Its point-stabilizer restriction uses that
same marking. The binary degree-gap theorem discharges both nontrivial
point-submodule branches, giving degree ten and hence the source degree-twelve
bound. Only the bound of thirty remains explicit: its source derivation belongs
to the independent involution-window argument. The conditional restriction APIs
remain available separately.

Source: Guralnick–Malle I, Proposition 5.1 and Theorem 6.6/Table 6.7;
Aschbacher–Smith, Chapter K, printed pp.451–452 and 457.
-/

public noncomputable section
open Representation
open _root_.Sporadic.Mathieu
open Representation.MathieuSmall.M22Recognition.DegreeThirty
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- The component representation transported through the specified marking. -/
abbrev simpleComponentAction (e : L ≃* M22) : Representation (ZMod 2) M22 V :=
  (ρ.comp L.subtype).comp e.symm.toMonoidHom

/-- The source gap through seventeen, excluding sixteen, with no unproved
restriction premise. The isomorphism is the supplied component marking. -/
theorem source_simple_finrank_eq_ten_of_le_seventeen_of_ne_sixteen
    [FiniteDimensional (ZMod 2) V] (h : SourceHypotheses ρ L) (e : L ≃* M22)
    (hd : Module.finrank (ZMod 2) V ≤ 17)
    (hne : Module.finrank (ZMod 2) V ≠ 16) : Module.finrank (ZMod 2) V = 10 := by
  let : (simpleComponentAction ρ L e).IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  exact finrank_eq_ten_of_le_seventeen_of_ne_sixteen (simpleComponentAction ρ L e)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective) hd hne

/-- The source action has degree ten or one of the two actual restriction branches. -/
theorem source_simple_degree_cases_of_le_thirty [FiniteDimensional (ZMod 2) V]
    (h : SourceHypotheses ρ L) (e : L ≃* M22)
    (hd : Module.finrank (ZMod 2) V ≤ 30) :
    Module.finrank (ZMod 2) V = 10 ∨
      ∃ S : Subrepresentation (pointRestriction (simpleComponentAction ρ L e)),
        S.toRepresentation.IsIrreducible ∧
          (Module.finrank (ZMod 2) S.toSubmodule = 9 ∨
            Module.finrank (ZMod 2) S.toSubmodule = 16) := by
  let : (simpleComponentAction ρ L e).IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  exact finrank_eq_ten_or_point_submodule (simpleComponentAction ρ L e)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective) hd

/-- Conditional source assembly on the same component marking. The two point
submodule premises remain to be proved; this is not the unconditional source gap. -/
theorem source_simple_finrank_le_twelve_of_point_submodule_cases
    [FiniteDimensional (ZMod 2) V] (h : SourceHypotheses ρ L) (e : L ≃* M22)
    (hd : Module.finrank (ZMod 2) V ≤ 30)
    (hnine : ∀ S : Subrepresentation (pointRestriction (simpleComponentAction ρ L e)),
      S.toRepresentation.IsIrreducible → Module.finrank (ZMod 2) S.toSubmodule = 9 →
        Module.finrank (ZMod 2) V = 10)
    (hsixteen : ∀ S : Subrepresentation (pointRestriction (simpleComponentAction ρ L e)),
      S.toRepresentation.IsIrreducible → Module.finrank (ZMod 2) S.toSubmodule = 16 → False) :
    Module.finrank (ZMod 2) V ≤ 12 := by
  let : (simpleComponentAction ρ L e).IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  have heq := finrank_eq_ten_of_point_submodule_cases (simpleComponentAction ρ L e)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective) hd hnine hsixteen
  omega

/-- The faithful irreducible component action has binary degree ten throughout
the explicit degree-thirty window, using exactly the supplied marking. -/
theorem source_simple_finrank_eq_ten_of_le_thirty
    [FiniteDimensional (ZMod 2) V] (h : SourceHypotheses ρ L) (e : L ≃* M22)
    (hd : Module.finrank (ZMod 2) V ≤ 30) : Module.finrank (ZMod 2) V = 10 := by
  let : (simpleComponentAction ρ L e).IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  exact finrank_eq_ten_of_le_thirty (simpleComponentAction ρ L e)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective) hd

/-- The source degree-twelve bound for the actual simple M22 component.
The independent source window supplies `hd`; no point-submodule premise remains. -/
theorem source_simple_finrank_le_twelve_of_le_thirty
    [FiniteDimensional (ZMod 2) V] (h : SourceHypotheses ρ L) (e : L ≃* M22)
    (hd : Module.finrank (ZMod 2) V ≤ 30) : Module.finrank (ZMod 2) V ≤ 12 := by
  rw [source_simple_finrank_eq_ten_of_le_thirty ρ L h e hd]
  decide

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
