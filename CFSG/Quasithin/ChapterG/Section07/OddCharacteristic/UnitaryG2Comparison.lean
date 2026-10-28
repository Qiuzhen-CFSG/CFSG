module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SU3.BinaryG2Comparison

/-!
# The PSU₃(3)–G₂(2)′ comparison in G.7

Transport the exceptional isomorphism through the actual projective
Hermitian matrix model specified by `ClassicalGroup.IsPSU`. Its parameter
three is the fixed-field order: the coefficient field has order nine,
conjugation is cube Frobenius, and the nondegenerate form is arbitrary.
The target is the actual commutator subgroup of the octonion automorphism
group over the two-element field.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.7.2(3) and G.7.3(1), printed p.348 / PDF p.359 in the combined
1 March 2004 manuscript. This comparison supplies the group identification;
the small-module assertions are proved by their separate consumers.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section07.OddCharacteristic

/-- Every genuine PSU₃(3) model is isomorphic to the binary octonion
commutator group, with no additional recognition or representation premise. -/
theorem psu33_nonempty_equiv_g2_derived {L : Type*} [Group L]
    (hmodel : ClassicalGroup.IsPSU L 3 3) :
    Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  exact ⟨e.trans (J.projectiveEquivBinaryG2Derived hcard hconj)⟩

end CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
