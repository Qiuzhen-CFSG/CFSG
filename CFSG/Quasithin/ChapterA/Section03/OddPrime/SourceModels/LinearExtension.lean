module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.LinearExtension.OuterData
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.LinearExtension.ChoiceEquivalences
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.LinearExtension.TwistedNorm

/-!
# The linear circle extension and its nonsplitting

The imported modules prove the compatible component identification, index
three, cardinality comparison, noncube existence, independent outer
parameters and choice equivalences for the literal A.3.16 carrier. Projective
cubic descent places every cube-one element in its marked component. Here
this gives the absence of a homomorphic section of the actual quotient map:
a section would lift every quotient element to a cube-one element of the
component and hence collapse a quotient of order three.

`linearCircle_no_section` discharges the containment premise of the preserved
conditional criterion. It assumes only the source field cardinality, positive
n and a noncube coefficient. The re-exported choice equivalences preserve
the original inner embedding for both order-three field choices and every
permitted diagonal representative.

Source: Aschbacher--Smith, Notation A.3.16, printed p.51.
-/

public section

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual index-three quotient has no homomorphic section once every
cube-one element belongs to its marked component. -/
theorem linearCircle_no_section_of_cube_mem {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a)
    (hcube : ∀ x : linearCircle F n a, x ^ 3 = 1 → x ∈ linearCircleComponent F n a) :
    ¬ ∃ s : (linearCircle F n a ⧸ linearCircleComponent F n a) →* linearCircle F n a,
      (QuotientGroup.mk' (linearCircleComponent F n a)).comp s = MonoidHom.id _ := by
  rintro ⟨s, hs⟩
  have hcard : Nat.card (linearCircle F n a ⧸ linearCircleComponent F n a) = 3 :=
    linearCircleComponent_index hn hc a ha
  have he : ∀ x : linearCircle F n a ⧸ linearCircleComponent F n a, x = 1 := by
    intro x
    have hx3 : x ^ 3 = 1 := by
      simpa only [hcard] using (pow_card_eq_one' (x := x))
    have hx : s x ∈ linearCircleComponent F n a :=
      hcube (s x) (by rw [← map_pow, hx3, map_one])
    have hh := (QuotientGroup.eq_one_iff _).mpr hx
    have hxs := DFunLike.congr_fun hs x
    exact hxs.symm.trans hh
  have : Subsingleton (linearCircle F n a ⧸ linearCircleComponent F n a) :=
    ⟨fun x y => (he x).trans (he y).symm⟩
  have := Nat.card_unique (α := linearCircle F n a ⧸ linearCircleComponent F n a)
  omega

/-- A.3.16's linear circle extension is nonsplit: the quotient by its
original marked component admits no homomorphic section. Cubic projective
descent supplies cube-one containment, so no splitting or outer-order
premise is required. -/
theorem linearCircle_no_section {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a) :
    ¬ ∃ s : (linearCircle F n a ⧸ linearCircleComponent F n a) →* linearCircle F n a,
      (QuotientGroup.mk' (linearCircleComponent F n a)).comp s = MonoidHom.id _ :=
  linearCircle_no_section_of_cube_mem hn hc a ha
    (linearCircle_cube_one_mem_component hn hc a ha)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
