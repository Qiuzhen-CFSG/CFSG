module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.FrattiniCoordinates
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.CoreRecognition

/-!
# Marked group recognition of the actual quartic hexad radical

The Frattini coordinates supply a central extension of the literal six-letter
augmentation core, together with its lifting A₆ action and a central generator
of order four. Intrinsic core-extension recognition now gives an actual group
equivalence to the even Clifford model, preserving the core projection, that
embedded generator and its square. The natural quotient equation follows from
the original Frattini-coordinate marking.

This discharges group recognition for the radical in Aschbacher–Smith I.2.2(6),
printed pp.410 and 412 / PDF pp.421 and 423. The comparison with the model's
signed A₆ action remains with the equivariant assembly.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover

namespace FrattiniCoordinates
variable {K : Type*} [Group K] [Finite K] [IsCyclic (center K)]
variable {e : (K ⧸ center K) ≃* M22} {B : Finset (Fin 22)} {hB : B ∈ m22Blocks}
variable (d : FrattiniCoordinates e hB) (hZ : Nat.card (center K) = 4)
include hZ

/-- Recognition of the literal radical, over both prescribed binary quotients,
with the ambient central generator and its square retained. -/
theorem exists_markedModelEquiv :
    ∃ c : center K, orderOf c = 4 ∧
      ∃ E : hexadRadical e B ≃* EvenCliffordSix.Model,
        (∀ r, EvenCliffordSix.projection (E r) = d.coreMap r) ∧
        E ⟨c.val, center_le_hexadRadical e B c.property⟩ = EvenCliffordSix.volume ∧
        E ((⟨c.val, center_le_hexadRadical e B c.property⟩ : hexadRadical e B) ^ 2) =
          EvenCliffordSix.involution ∧
        (∀ r, EvenCliffordSix.naturalProjection (E r) = Binary.naturalMap e hB r) := by
  obtain ⟨c, hc, D, hp, _, hv, hs⟩ := d.exists_coreExtension hZ
  refine ⟨c, hc, D.modelEquiv, ?_, ?_, ?_, ?_⟩
  · intro r
    rw [D.modelEquiv_projection, hp]
  · have hv' : (⟨c.val, center_le_hexadRadical e B c.property⟩ : hexadRadical e B) =
        D.volume := Subtype.ext hv.symm
    rw [hv', D.modelEquiv_volume]
  · have hs' : (⟨c.val, center_le_hexadRadical e B c.property⟩ : hexadRadical e B) ^ 2 =
        D.sign := Subtype.ext hs.symm
    rw [hs', D.modelEquiv_sign]
  · intro r
    apply Multiplicative.toAdd.injective
    change BinaryPermutation.coreToNatural (Fin 6) (D.modelEquiv r).vector = _
    have hr := congrArg Multiplicative.toAdd (D.modelEquiv_projection r)
    change (D.modelEquiv r).vector = (D.projection r).toAdd at hr
    rw [hr, hp]
    exact d.natural_projection r

end FrattiniCoordinates
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
