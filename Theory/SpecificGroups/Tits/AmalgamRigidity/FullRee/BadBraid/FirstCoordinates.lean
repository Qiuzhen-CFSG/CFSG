module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Relators
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.FirstRestrictions.Generators
/-!
# The Suzuki endpoint words in actual core coordinates

The computable semidirect product retains the verified first-endpoint map.
Its four specified elements satisfy all twenty-two local words by ordinary
kernel reduction of the established group operations. The source maps in
the next extension transport these equations to a faithful completion.

Source: Shinoda (1975), pp.81–83; Aschbacher–Smith F.4.8 and F.4.17.
-/
@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid
open ReeTwo Subgroup.CosetWordCertificate FirstRestrictions
def firstGens : Nat → E
 | 0 => SemidirectProduct.inr FiveFour.a⁻¹
 | 1 => SemidirectProduct.inl (Core.root 0)
 | 2 => SemidirectProduct.inl (Core.root 2)
 | 3 => SemidirectProduct.inr FiveFour.r
 | _ => 1

theorem first_relations : ∀ i : Fin 22,
    eval firstGens (relator ⟨i.val, by omega⟩) = 1 := by
  decide +kernel

end Tits.AmalgamRigidity.FullRee.BadBraid
