module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Literal
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model

/-!
# Faithful coefficients on the literal Hall--Janko corner

Evaluate a corner element at the 1008 fixed double-coset representatives.
Left and right subgroup invariance prove injectivity from geometric coverage.
Expanding the right norm reduces multiplication by each literal generator to
25 coefficient evaluations per word. A finite arithmetic certificate then
identifies those evaluations with the exact existing operator rows.

`literalCoordinates_of_certificates` is the complete conditional application
to `LiteralCoordinates`. This task retains its final assembly: the geometric
identification and finite coefficient certificate still need producers.
Source: Guralnick--Malle Proposition 5.1 and the retained ATLAS coset discovery;
see Presentation/Coordinates/source/README.md for precise conventions.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
open Sporadic.LeechRelated.J2
open CoefficientTheory OrbitData
local instance : Fintype subgroup := Fintype.ofFinite subgroup

/-- Evaluate actual group-algebra coefficients at the fixed double-coset representatives. -/
def literalCoordinateMap (he : IsIdempotentElem (fiveNorm subgroup)) :
    he.Corner →+ Coordinates where
  toFun z i := z.val.coeff (representative i)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem literalCoordinateMap_coeff (C : RightCosetGeometry)
    (he : IsIdempotentElem (fiveNorm subgroup)) (z : he.Corner) (g : Carrier) :
    z.val.coeff g = literalCoordinateMap he z (orbit (C.coset g)) := by
  obtain ⟨p, q, hg⟩ := C.double_cover g
  change z.val.coeff g = z.val.coeff (representative (orbit (C.coset g)))
  conv_lhs => rw [hg]
  exact coeff_double he z p q _

theorem literalCoordinateMap_injective (C : RightCosetGeometry)
    (he : IsIdempotentElem (fiveNorm subgroup)) :
    Function.Injective (literalCoordinateMap he) := by
  intro z z' h
  apply Subtype.ext
  apply MonoidAlgebra.ext
  ext g
  rw [literalCoordinateMap_coeff C, literalCoordinateMap_coeff C, h]

theorem literalCoordinateMap_one (C : RightCosetGeometry)
    (he : IsIdempotentElem (fiveNorm subgroup)) : literalCoordinateMap he 1 = seed := by
  classical
  ext i
  change (fiveNorm subgroup).coeff (representative i) = _
  rw [norm_coeff, C.representative_mem_iff]
  by_cases hi : i = 0 <;> simp [seed, hi]

private theorem sum_by_label (v : Coordinates) (f : PowerIndex → Fin 1008) :
    (∑ t, v (f t)) = ∑ i : Fin 1008, v i * ∑ t : PowerIndex,
      if f t = i then (1 : ZMod 2) else 0 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp [mul_ite, eq_comm]

theorem literalCoordinateMap_condensed (C : RightCosetGeometry)
    (he : IsIdempotentElem (fiveNorm subgroup)) (z : he.Corner)
    (w : List (Fin 4)) (j : Fin 1008) :
    literalCoordinateMap he (z * condensed he (word w)) j =
      ∑ i : Fin 1008, literalCoordinateMap he z i * wordEntry w i j := by
  change (z * condensed he (word w)).val.coeff (representative j) = _
  rw [coeff_mul_condensed]
  rw [← (subgroupEquiv.sum_comp (fun p : subgroup =>
    z.val.coeff (representative j * (p : Carrier) * (word w)⁻¹)))]
  calc
    _ = ∑ t : PowerIndex, literalCoordinateMap he z
        (orbit (walk (inverseWord w) (walk (subgroupWord t) (root j)))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [literalCoordinateMap_coeff C]
      change literalCoordinateMap he z
        (orbit (C.coset (representative j * (subgroupElement t : Carrier) * (word w)⁻¹))) = _
      rw [← word_subgroupWord, ← word_inverseWord, C.coset_word, C.coset_word,
        C.coset_representative]
    _ = _ := sum_by_label (literalCoordinateMap he z) _

private theorem literalCoordinateMap_list (C : RightCosetGeometry)
    (he : IsIdempotentElem (fiveNorm subgroup)) (z : he.Corner)
    (ws : List (List (Fin 4))) (j : Fin 1008) :
    literalCoordinateMap he (z * (ws.map fun w => condensed he (word w)).sum) j =
      ∑ i : Fin 1008, literalCoordinateMap he z i *
        (ws.map fun w => wordEntry w i j).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, map_add, Pi.add_apply,
      Finset.sum_add_distrib, literalCoordinateMap_condensed C, ih]

theorem literalCoordinateMap_generators (C : RightCosetGeometry)
    (hcoeff : CoefficientCertificate)
    (he : IsIdempotentElem (fiveNorm subgroup)) (z : he.Corner) (k : Fin 9) :
    literalCoordinateMap he (z * generators he k) = operator k (literalCoordinateMap he z) := by
  ext j
  simp only [operator, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [generators, literalCoordinateMap_list C]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (literalCoordinateMap he z i * ·) (hcoeff k i j)

/-- The actual corner-coordinate contract follows from geometric identification
of the saved cosets and the independent finite coefficient checks. Both premises
remain genuine obligations; this theorem does not assert them. -/
theorem literalCoordinates_of_certificates (C : RightCosetGeometry)
    (hcoeff : CoefficientCertificate) : LiteralCoordinates := by
  intro he
  exact ⟨literalCoordinateMap he, literalCoordinateMap_injective C he,
    literalCoordinateMap_one C he, literalCoordinateMap_generators C hcoeff he⟩

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
