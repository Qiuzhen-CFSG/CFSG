module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.SmallRange
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.Reciprocity
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.ModelClassification
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads

/-!
# The nine-dimensional point-submodule branch for M22

For the full degree-thirty range, the classification of binary nine-dimensional
point modules identifies the given simple submodule with one of the two
concrete Hermitian models. This actual equivalence produces an induced surjection.
Its maximal kernel realizes the ambient degree as the degree of an actual
simple quotient of that fixed induced module. Faithfulness rules out the
one-dimensional alternative, and the source bound rules out degrees above
thirty.

The checked model comparison and induced filtrations discharge both inputs
in `finrank_eq_ten`. The proof retains arbitrary nonsplit extensions and
does not assume absolute irreducibility of the given binary modules.

Source: Guralnick–Malle I, Proposition 5.1, pp.15–16 and Theorem 6.6/Table 6.7;
Aschbacher–Smith, Chapter K, printed pp.451–452 and 457.
-/

public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Frobenius reciprocity connects the actual nine-subspace inclusion with the
concrete head calculation, keeping both inputs explicit for reuse. -/
theorem finrank_eq_ten_of_model_equiv_and_smallInducedHeads
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M22 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 30)
    (S : Subrepresentation (pointRestriction σ))
    (b : Bool) (e : S.toRepresentation.Equiv (Models.pointAction b))
    (hheads : SmallInducedHeads) : Module.finrank (ZMod 2) V = 10 := by
  obtain ⟨f, hsurj⟩ := exists_surjective_induced_of_equiv σ S b e
  have h := hheads b f.ker (SimpleHeadQuotient.isCoatom_ker_of_surjective f hsurj)
  have hdim := (f.toLinearMap.quotKerEquivOfSurjective hsurj).finrank_eq
  change Module.finrank (ZMod 2) (Models.InducedSpace b ⧸ f.ker.toSubmodule) =
    Module.finrank (ZMod 2) V at hdim
  rw [hdim] at h
  have hlo := BinaryPrimeDegree.orderOf_le_finrank σ hf
    (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) (by rw [m22_order]; norm_num)
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
  omega

/-- A faithful irreducible binary M22 module of dimension at most thirty
containing an irreducible nine-dimensional point-stabilizer submodule has
dimension ten. The restriction uses the actual stabilizer inclusion. -/
theorem finrank_eq_ten [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M22 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 30)
    (S : Subrepresentation (pointRestriction σ)) [S.toRepresentation.IsIrreducible]
    (hS : Module.finrank (ZMod 2) S.toSubmodule = 9) :
    Module.finrank (ZMod 2) V = 10 := by
  obtain ⟨b, ⟨e⟩⟩ := exists_point_model_equiv S.toRepresentation hS
  exact finrank_eq_ten_of_model_equiv_and_smallInducedHeads σ hf hd S b e smallInducedHeads

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule
