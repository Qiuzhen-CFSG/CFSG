module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits

/-!
# The full automorphism group of the ATLAS Hall--Janko carrier

The proved first-generator fusion and second-generator centralizer orbits
make the faithful conjugation action of the concrete permutation extension
surjective. Its resulting equivalence with the full automorphism group sends
the original carrier inclusion to inner automorphisms. This is the ambient
equivalence used to transport the marked exceptional parabolics.

Source: the retained ATLAS `J2G1-p100B0` permutations, GLS3 Table 5.3g, and
Aschbacher--Smith F.1.12(I)(11), printed p.263 (PDF p.274).
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.ExceptionalParabolics
open GeneratorPair

/-- Every automorphism of the actual degree-100 carrier comes from the extension. -/
theorem extensionAction_surjective : Function.Surjective extensionAction :=
  extensionAction_surjective_of_pair_calculations
    first_generator_conjugate second_generator_orbits

/-- The concrete permutation extension is the full automorphism group. -/
noncomputable def extensionEquivAut : Extension ≃* MulAut Carrier :=
  extensionEquivAut_of_pair_calculations first_generator_conjugate second_generator_orbits

@[simp] theorem extensionEquivAut_apply (g : Extension) :
    extensionEquivAut g = extensionAction g := rfl

@[simp] theorem extensionEquivAut_intoExtension (g : Carrier) :
    extensionEquivAut (intoExtension g) = MulAut.conj g :=
  extensionAction_inner g

@[simp] theorem extensionEquivAut_involution :
    extensionEquivAut extensionInvolution = involutionAut := rfl

/-- Transport through the literal inclusion is exactly the inner-automorphism map. -/
theorem extensionEquivAut_comp_intoExtension :
    extensionEquivAut.toMonoidHom.comp intoExtension = MulAut.conj :=
  MonoidHom.ext extensionEquivAut_intoExtension

end Sporadic.LeechRelated.J2.ExceptionalParabolics
