module

public import Theory.Representation.MathieuCodeRestriction.Duality
public import Theory.Representation.MathieuCodeRestriction.Duality.Absolute.Irreducibility
public import Theory.Representation.MathieuCodeRestriction.Duality.Absolute.PrimeDimension

/-!
# Absolute irreducibility of the native Mathieu code and cocode

The four eleven-dimensional actions are irreducible by simplicity, the
vanishing 23-cycle norm, and the binary order-23 degree bound. Their prime
dimension and faithfulness now force absolute irreducibility: a larger
endomorphism field would make the acting group abelian. The native groups
are nonabelian, since a simple abelian group has prime order.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.13.2,
printed p.395, for the M₂₃ and M₂₄ cases. These statements concern the actual
quotient actions defined in H.13.1, including the native M₂₃ embedding.
-/

public section

open Representation Sporadic.Mathieu
namespace MathieuCode

private theorem m24_nonabelian : ¬ IsMulCommutative M24 := by
  intro h
  let : IsMulCommutative M24 := h
  have hp := Group.is_simple_iff_prime_card.mp m24_isSimpleGroup
  rw [m24_order] at hp
  norm_num at hp

private theorem m23_nonabelian : ¬ IsMulCommutative M23 := by
  intro h
  let : IsMulCommutative M23 := h
  have hp := Group.is_simple_iff_prime_card.mp m23_isSimpleGroup
  rw [m23_order] at hp
  norm_num at hp

/-- H.13.2 for the eleven-dimensional M₂₄ code quotient. -/
theorem code_isAbsolutelyIrreducible : codeRepresentation.IsAbsolutelyIrreducible := by
  let : codeRepresentation.IsIrreducible := code_isIrreducible
  exact isAbsolutelyIrreducible_of_prime_finrank_of_faithful codeRepresentation code_faithful
    (by rw [finrank_code]; decide) m24_nonabelian

/-- H.13.2 for the eleven-dimensional M₂₄ cocode quotient. -/
theorem cocode_isAbsolutelyIrreducible : cocodeRepresentation.IsAbsolutelyIrreducible := by
  let : cocodeRepresentation.IsIrreducible := cocode_isIrreducible
  exact isAbsolutelyIrreducible_of_prime_finrank_of_faithful cocodeRepresentation cocode_faithful
    (by rw [finrank_cocode]; decide) m24_nonabelian

/-- H.13.2 for the code restricted to the actual native M₂₃ point stabilizer. -/
theorem m23Code_isAbsolutelyIrreducible : m23CodeRepresentation.IsAbsolutelyIrreducible := by
  let : m23CodeRepresentation.IsIrreducible := m23Code_isIrreducible
  exact isAbsolutelyIrreducible_of_prime_finrank_of_faithful m23CodeRepresentation m23Code_faithful
    (by rw [finrank_code]; decide) m23_nonabelian

/-- H.13.2 for the cocode restricted to the actual native M₂₃ point stabilizer. -/
theorem m23Cocode_isAbsolutelyIrreducible : m23CocodeRepresentation.IsAbsolutelyIrreducible := by
  let : m23CocodeRepresentation.IsIrreducible := m23Cocode_isIrreducible
  exact isAbsolutelyIrreducible_of_prime_finrank_of_faithful m23CocodeRepresentation
    m23Cocode_faithful (by rw [finrank_cocode]; decide) m23_nonabelian

end MathieuCode
