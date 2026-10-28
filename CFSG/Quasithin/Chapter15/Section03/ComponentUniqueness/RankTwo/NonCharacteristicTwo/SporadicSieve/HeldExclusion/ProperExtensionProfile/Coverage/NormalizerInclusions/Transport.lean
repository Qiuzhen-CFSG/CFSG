module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Candidates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.Representatives
public import Theory.SpecificGroups.Held.LocalPairs.Transport
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Full normalizers of the inner Held images

Centerlessness identifies normalization of an actual inner-automorphism image
with preservation of the original subgroup. Stabilizer transport then keeps
conjugation compatible with the two literal local candidates. In particular,
every automorphism preserving a subgroup also preserves its full inner normalizer.

These are transport lemmas, with no finite coverage assertion. Source application:
Aschbacher--Smith 15.3.41--42, printed p.1138, and GLS3 Table 5.3p.
-/

public section
open Subgroup Held.LocalPairs
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions
open CoverageData

/-- The actual inner image has exactly the full automorphism stabilizer as normalizer. -/
theorem innerImage_normalizer (U : Subgroup Held.He) :
    normalizer (U.map MulAut.conj : Set (MulAut Held.He)) = automorphismNormalizer U := by
  ext a
  rw [mem_normalizer_iff_map_conj_eq]
  change (U.map MulAut.conj).map (MulAut.conj a).toMonoidHom = U.map MulAut.conj ↔
    U.map a.toMonoidHom = U
  have he : (U.map MulAut.conj).map (MulAut.conj a).toMonoidHom =
      (U.map a.toMonoidHom).map MulAut.conj := by
    rw [map_map, map_map]
    congr 1
    ext x y
    simp
  rw [he]
  exact ⟨fun h => map_injective
    (Theory.GroupTheory.conj_injective_of_center_eq_bot center_eq_bot) h,
    fun h => congrArg (map MulAut.conj) h⟩

/-- Specialization to the four published literal rows. -/
theorem ambientRow_normalizer (j : Fin 4) :
    normalizer (ambientRow j : Set (MulAut Held.He)) = automorphismNormalizer (heldRow j) :=
  innerImage_normalizer _

/-- Conjugation of a literal subgroup transports its full automorphism stabilizer. -/
theorem automorphismNormalizer_map (U : Subgroup Held.He) (a : MulAut Held.He) :
    automorphismNormalizer (U.map a.toMonoidHom) =
      (automorphismNormalizer U).map (MulAut.conj a).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj a U

/-- An automorphism preserving a subgroup preserves its full inner normalizer. -/
theorem automorphismNormalizer_le_innerNormalizer (U : Subgroup Held.He) :
    automorphismNormalizer U ≤ automorphismNormalizer (normalizer (U : Set Held.He)) := by
  intro a ha
  change U.map a.toMonoidHom = U at ha
  change (normalizer (U : Set Held.He)).map a.toMonoidHom = _
  rw [map_equiv_normalizer_eq, ha]

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions
