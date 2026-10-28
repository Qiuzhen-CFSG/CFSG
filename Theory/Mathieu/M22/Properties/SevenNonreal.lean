module
public import Theory.Mathieu.M24.Properties.SevenNonreal
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility

/-!
# Nonreal seven-elements of Aut(M22)

The proved pair-stabilizer realization embeds the full abstract automorphism
group in the native M24. The binary cocode trace obstruction there therefore
excludes real seven-elements in Aut(M22). This uses the actual group
isomorphism and inclusion, not an identification of family names.

Source application: the two J4 involution-centralizer quotients in
Aschbacher--Smith 12.1.1, printed p.788; ATLAS M22 automorphism realization.
-/

public noncomputable section
namespace Sporadic.Mathieu.SevenNonreal

/-- The actual pair-stabilizer realization transfers nonreality to Aut(M22). -/
theorem aut_m22_not_real (x : MulAut M22) (hx : orderOf x = 7) : ¬ IsConj x x⁻¹ := by
  let f : MulAut M22 →* M24 := MathieuCode.m22PairStabilizer.subtype.comp
    MathieuCode.m22PairStabilizerEquivAut.symm.toMonoidHom
  have hi : Function.Injective f :=
    MathieuCode.m22PairStabilizer.subtype_injective.comp
      MathieuCode.m22PairStabilizerEquivAut.symm.injective
  intro hr
  exact not_real (f x) ((orderOf_injective f hi x).trans hx)
    (by simpa only [map_inv] using f.map_isConj hr)
end Sporadic.Mathieu.SevenNonreal
