module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.Preparation
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve

/-!
# The degree-twenty-four window for the actual triple Mathieu cover

Every faithful irreducible binary action of the actual triple cover with degree
at most twenty-four has degree twelve. The central element equips the same
space with F₄ scalars, preserving faithfulness and irreducibility, and preparation
leaves only F₄ degrees six, nine and twelve. The two proved representation
exclusions remove nine and twelve. Thus the surviving action has F₄ degree six,
without assuming absolute irreducibility or prescribing its Schur field.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
pp.15–16 and Theorem 6.6/Table 6.7; Aschbacher–Smith H.12.1, pp.393–394.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) M22TripleCover V) [ρ.IsIrreducible]
  (hf : Function.Injective ρ)

include hf in
/-- The arbitrary-module binary degree gap for the actual triple Mathieu cover. -/
theorem finrank_eq_twelve_of_le_twenty_four
    (hd : Module.finrank (ZMod 2) V ≤ 24) : Module.finrank (ZMod 2) V = 12 :=
  finrank_eq_twelve_of_field_exclusions ρ hf
    centralFieldDegreeExclusion_nine centralFieldDegreeExclusion_twelve hd

/-- The same action has degree six over the field supplied by its central scalar. -/
theorem field_finrank_eq_six_of_le_twenty_four
    (hd : Module.finrank (ZMod 2) V ≤ 24) :
    letI := Uniqueness.PointRestriction.fieldModule ρ hf
    Module.finrank Uniqueness.PointRestriction.F V = 6 := by
  let := Uniqueness.PointRestriction.fieldModule ρ hf
  have ht := twice_field_finrank ρ hf
  have hd' := finrank_eq_twelve_of_le_twenty_four ρ hf hd
  omega

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
