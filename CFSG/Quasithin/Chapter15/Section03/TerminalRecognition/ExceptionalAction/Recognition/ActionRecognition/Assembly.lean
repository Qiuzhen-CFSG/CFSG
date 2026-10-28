module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.ExceptionalCase
public import Theory.Representation.HexacodeAction.TerminalIrreducible
public import Theory.Representation.Quotient

/-!+# Transport from intrinsic representation recognition to the source action

An exceptional case puts the actual quotient action on the concrete hexacode
group, preserving faithfulness and irreducibility on its even cover. An
intrinsic recognition of that representation may twist the actor by an
automorphism. The even cover is the commutator subgroup, so the twist preserves
it; the Thompson-image equality therefore survives the same transport.

This is the assembly map for two independent obligations: the ordinary FF
exclusions must construct `ExceptionalCase`, and intrinsic representation
recognition must provide the intertwining coordinates. Neither obligation is
assumed to have been discharged by the transport lemmas here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453, and the final proof of 15.3.1, printed p.1155.
-/

@[expose] public section

open Subgroup Atlas.Codes
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition
namespace ExceptionalCase

variable {H : Type*} [Group H] [Finite H]
    {V : Subgroup H} [IsElementaryAbelian 2 (moduleClosure V)]
    {d : SourceInput V} (c : ExceptionalCase d)

/-- The actual action transported to the concrete full group, on the original
vector space. No vector coordinates have been selected yet. -/
noncomputable def modelAction :
    Representation (ZMod 2) HexAutomorphisms (Additive (moduleClosure V)) :=
  (quotientAction V d.centralizer_isTwoGroup d.core_centralizes).comp
    c.actor.symm.toMonoidHom

omit [Finite H] in
/-- Transport along the actor equivalence preserves faithfulness. -/
theorem modelAction_injective : Function.Injective c.modelAction :=
  (quotientAction_injective V d.centralizer_isTwoGroup d.core_centralizes).comp
    c.actor.symm.injective

omit [Finite H] in
/-- The even restriction uses the literal inclusion of the offender subgroup. -/
theorem offenderEquiv_symm_coe (g : HexEvenAutomorphisms) :
    (c.offenderEquiv.symm g : coreQuotient H) = c.actor.symm g := by
  apply c.actor.injective
  rw [c.actor.apply_symm_apply]
  exact congrArg Subtype.val (c.offenderEquiv.apply_symm_apply g)

omit [Finite H] in
/-- The transported even action is precisely the source offender action. -/
theorem modelAction_even :
    c.modelAction.comp hexSign.ker.subtype =
      d.offenderAction.comp c.offenderEquiv.symm.toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change quotientAction V d.centralizer_isTwoGroup d.core_centralizes (c.actor.symm g) v =
    quotientAction V d.centralizer_isTwoGroup d.core_centralizes
      (c.offenderEquiv.symm g : coreQuotient H) v
  rw [c.offenderEquiv_symm_coe]

omit [Finite H] in
/-- The intrinsic recognition problem has an irreducible even restriction. -/
theorem modelAction_even_irreducible :
    Representation.IsIrreducible (c.modelAction.comp hexSign.ker.subtype) := by
  rw [c.modelAction_even]
  exact (Representation.irreducible_comp_surjective_iff c.offenderEquiv.symm.toMonoidHom
    c.offenderEquiv.symm.surjective d.offenderAction).mpr c.irreducible

/-- Intrinsic intertwining coordinates give the required source coordinates.
Automorphism twists are allowed, since they preserve the even cover. -/
noncomputable def coordinatesOfModelEquivalence
    (a : MulAut HexAutomorphisms)
    (e : Additive (moduleClosure V) ≃ₗ[ZMod 2] hexacode)
    (he : ∀ g v, e (c.modelAction g v) = Representation.Hexacode.action (a g) (e v)) :
    HexacodeCoordinates V d.centralizer_isTwoGroup d.core_centralizes where
  actor := c.actor.trans a
  vectors := e
  equivariant g v := by
    change e (quotientAction V d.centralizer_isTwoGroup d.core_centralizes g v) =
      Representation.Hexacode.action (a (c.actor g)) (e v)
    have h := he (c.actor g) v
    change e (quotientAction V d.centralizer_isTwoGroup d.core_centralizes
      (c.actor.symm (c.actor g)) v) = _ at h
    rwa [c.actor.symm_apply_apply] at h
  thompson_image := by
    change ((thompsonGroup H).map coreProjection).map
      (a.toMonoidHom.comp c.actor.toMonoidHom) = hexSign.ker
    rw [← Subgroup.map_map, c.thompson_image, Representation.Hexacode.even_map_automorphism]

end ExceptionalCase
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition
