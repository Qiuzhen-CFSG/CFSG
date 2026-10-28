module

public import Theory.Representation.G2BinarySylowFixedSpace
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.G2OrthogonalCover.Universal

/-!
# Fixed points and central covers of the binary G₂ natural module

Every Sylow 2-subgroup of G₂(2)′ fixes at most a line on the natural six-space.
Conjugacy transports the explicit parabolic Sylow calculation to any Sylow.
The dual first cohomology is one-dimensional, so a perfect central cover
has at most a one-dimensional kernel.

These are the model bounds used in the G₂ block case of Aschbacher–Smith
3.3.27–31 and its 12.2.16 normalizer consumer.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace Atlas.G2.Natural.BinarySylowFixedSpace
open Atlas.G2.BinaryParabolicPair

theorem card_derived_sylow_fixed_le_two (P : Sylow 2 (commutator (Atlas.G2.Model (ZMod 2)))) :
    Nat.card (fixedSpace (g2DerivedNatural (ZMod 2)) (P : Subgroup (commutator (Atlas.G2.Model (ZMod 2))))) ≤ 2 := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq (commutator (Atlas.G2.Model (ZMod 2))) (show Sylow 2 (commutator (Atlas.G2.Model (ZMod 2))) from derivedSylow) P
  rw [Sylow.coe_subgroup_smul]
  change Nat.card (fixedSpace (g2DerivedNatural (ZMod 2))
    ((derivedSylow : Subgroup (commutator (Atlas.G2.Model (ZMod 2)))).map (MulAut.conj g).toMonoidHom)) ≤ 2
  rw [←Nat.card_congr (fixedSpaceConjEquiv (g2DerivedNatural (ZMod 2))
    (derivedSylow : Subgroup (commutator (Atlas.G2.Model (ZMod 2)))) g).toEquiv]
  let f : fixedSpace (g2DerivedNatural (ZMod 2)) (derivedSylow : Subgroup (commutator (Atlas.G2.Model (ZMod 2)))) → ZMod 2 :=
    fun v => binaryCoordinates (ZMod 2) v.val 0
  have hf : Function.Injective f := by
    intro v w hh
    apply Subtype.ext
    apply binaryCoordinates_injective (ZMod 2)
    rw [derivedSylow_fixed_coordinates v.val v.property,
      derivedSylow_fixed_coordinates w.val w.property]
    exact congrArg (fun a : ZMod 2 => ![a,0,0,0,0,0]) hh
  exact (Nat.card_le_card_of_injective f hf).trans_eq (Nat.card_zmod 2)
end Atlas.G2.Natural.BinarySylowFixedSpace

namespace Atlas.G2.Natural.BinarySylowFixedSpace

/-- The central-cover bound for the literal binary derived natural action. -/
theorem derived_natural_dual_H1_finrank :
    Module.finrank (ZMod 2) (H1 (g2DerivedNatural (ZMod 2)).dual) = 1 := by
  have he : OrthogonalCover.binaryNatural (ZMod 2) = g2DerivedNatural (ZMod 2) := by
    ext g v
    rfl
  rw [←he]
  simpa only [Module.finrank_self] using OrthogonalCover.binary_dual_H1_finrank (ZMod 2)

end Atlas.G2.Natural.BinarySylowFixedSpace
