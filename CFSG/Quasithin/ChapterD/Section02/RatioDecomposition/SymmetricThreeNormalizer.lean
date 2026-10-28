module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Embedded
public import Theory.Representation.BinarySymmetricThreeNormalizer

/-!
# The actual symmetric-three factor normalizer

The D.2.16 factor carries its faithful action and full commutator support.
In the four-dimensional symmetric-three branch these discharge the inputs
to the literal linear-normalizer theorem. Every intermediate action image
containing the factor and a four-subgroup is S₃ × C₂ or S₃ × S₃.

Source: Aschbacher--Smith, 15.1.2, proper seed-span case, printed p.1085.
The existence of the reducible factor is supplied by the original orbit
seed argument, rather than included as a premise in the linear theorem.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (F : Factor ρ)

/-- The literal linear normalizer of the classified source factor has order
dividing 36. The factor's full commutator support supplies cubic fixed-freeness. -/
theorem symmetricThree_normalizer_card_dvd
    (hdim : Module.finrank (ZMod 2) F.Space = 4)
    (e : F.Carrier ≃* Equiv.Perm (Fin 3)) :
    Nat.card (normalizer (F.action.asGroupHom.range : Set (Module.End (ZMod 2) F.Space)ˣ)) ∣ 36 :=
  BinarySymmetricThreeNormalizer.linear_normalizer_card_dvd_of_equiv
    F.action F.faithful hdim e F.full

/-- The original overgroup of the actual factor image has the two source
possibilities once its Sylow action contains a four-subgroup. -/
theorem symmetricThree_normalizer_overgroup_cases
    (hdim : Module.finrank (ZMod 2) F.Space = 4)
    (e : F.Carrier ≃* Equiv.Perm (Fin 3))
    (A : Subgroup (Module.End (ZMod 2) F.Space)ˣ)
    (hFA : F.action.asGroupHom.range ≤ A)
    (hAN : A ≤ normalizer (F.action.asGroupHom.range : Set (Module.End (ZMod 2) F.Space)ˣ))
    (hfour : 4 ∣ Nat.card A) :
    Nonempty (A ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) ∨
      Nonempty (A ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
  BinarySymmetricThreeNormalizer.linear_normalizer_overgroup_cases
    F.action F.faithful hdim e F.full A hFA hAN hfour

end CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
