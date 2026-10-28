module
public import Theory.Representation.OrbitSizeSeparation
public import Theory.Representation.HexacodeAction.TerminalIrreducible
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.Operators

/-!
# Two nonzero orbits of the actual even hexacode action

The two existing even generators act on the three field coordinates by
explicit operators. A small word table carries one of two nonzero seeds
to every nonzero coordinate vector. The certificate checks only the 64
vectors in F₄³, and its words are then interpreted in the actual even
hexacode group. Since the code has even cardinality, its two nonzero
orbits have unequal sizes.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 12.2.16,
printed pp.799–800, and K.1.3, p.453. The underlying code and monomial
generators retain the ATLAS attribution through the imported modules;
see LICENSES/ATLAS.txt. The word table is derived from those generators.
-/

public noncomputable section
open Atlas.Codes
namespace Representation.Hexacode
open SixDimensional.EvenImage

private def coordinateStep (b : Bool) (x : Fin 3 → F) : Fin 3 → F :=
  if b then ![x 2, omega * x 0, omega ^ 2 * x 1]
  else ![x 0 + x 1 + x 2, x 0, x 1]

private def coordinateWord (l : List Bool) (x : Fin 3 → F) : Fin 3 → F :=
  l.foldr coordinateStep x

private def groupWord (l : List Bool) : HexEvenAutomorphisms :=
  (l.map fun b => if b then generatorB else generatorA).prod

private theorem word_coordinates (l : List Bool) (v : hexacode) :
    binaryCoordinates (evenAction (groupWord l) v) =
      coordinateWord l (binaryCoordinates v) := by
  induction l with
  | nil => simp [groupWord,coordinateWord]
  | cons b l ih =>
      simp only [groupWord,List.map_cons,List.prod_cons,map_mul,Module.End.mul_apply]
      change binaryCoordinates (evenAction (if b then generatorB else generatorA)
        (evenAction (groupWord l) v)) = _
      cases b
      · simp only [Bool.false_eq_true,ite_false]
        rw [show binaryCoordinates (evenAction generatorA (evenAction (groupWord l) v)) =
          ![binaryCoordinates (evenAction (groupWord l) v) 0 +
              binaryCoordinates (evenAction (groupWord l) v) 1 +
              binaryCoordinates (evenAction (groupWord l) v) 2,
            binaryCoordinates (evenAction (groupWord l) v) 0,
            binaryCoordinates (evenAction (groupWord l) v) 1] from
          generatorA_coordinates _]
        rw [ih]
        rfl
      · simp only [ite_true]
        rw [show binaryCoordinates (evenAction generatorB (evenAction (groupWord l) v)) =
          ![binaryCoordinates (evenAction (groupWord l) v) 2,
            omega * binaryCoordinates (evenAction (groupWord l) v) 0,
            omega ^ 2 * binaryCoordinates (evenAction (groupWord l) v) 1] from
          generatorB_coordinates _]
        rw [ih]
        rfl

private def vectorCode (x : Fin 3 → F) : Fin 64 :=
  Fin.ofNat 64 ((x 0).re.val + 2*(x 0).im.val + 4*(x 1).re.val +
    8*(x 1).im.val + 16*(x 2).re.val + 32*(x 2).im.val)

private def wordTable : Fin 64 → List Bool :=
  ![[],
    [],
    [false,false,false,true,false,true,false],
    [false,false,true,false,true,false,false],
    [true,false,false,true,false,true,false,false],
    [false],
    [false,true,false,false],
    [false,false,true,false],
    [true],
    [false,false,true,true,false,true,false],
    [true,false,true,false],
    [true,true,false,false],
    [false,true,true,false,false,true,false],
    [false,true,true,false,true,false,false],
    [true,false,true],
    [true,false,true,true,false,true,false],
    [true,true],
    [false,true,false,false,true,false,true,false,false],
    [false,true,false,false,true,false],
    [true,true,false],
    [false,false],
    [true,false,false,true,false,false],
    [],
    [false,false,true],
    [true,false,false,true,true,false,true,false],
    [false,true,false,true,true],
    [false],
    [false,false,true,false,false],
    [true,true,false,true,false],
    [true,false],
    [false,false,false,true,false],
    [false,false,false,true],
    [false,false,true,false,true,false],
    [false,true,false],
    [false,true],
    [true,true,false,true,false,false],
    [false,false,true,false,true],
    [false,false,false],
    [true,false,true,true],
    [false,false,false,true,true,false,true,false],
    [false,true,false,true,false],
    [false,false],
    [true,false,true,true,false,false],
    [true,true],
    [true,true,false,true],
    [false,true,true,false,false],
    [false,true,false,true],
    [false,true,true],
    [false,true,false,true,false,false],
    [true,false,false],
    [false,true,true,false,true,false],
    [true,true,false,false,true,false],
    [true,false,false,true,false],
    [false,true],
    [false,false,true,true,false,true,false,false],
    [false,true,false],
    [true,false],
    [false,true,false,true],
    [true,false,false,false],
    [true,false,true],
    [true,false,true,false,false],
    [true],
    [false,false,true,true],
    [true,false,false,true,true,false,true,false,false]]

private def secondOrbit : Fin 64 → Bool :=
  ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,true,false,false,true,false,true,false,false,false,false,false,true,true,false,false,true,false,true,false,false,true,true,false,false,false,false,false,true,false,true,false,false,true,true,false,true,true,false]

private def firstVector : Fin 3 → F := ![1,0,0]
private def secondVector : Fin 3 → F := ![omega,1,1]

private theorem coordinate_cover : ∀ x : Fin 3 → F, x ≠ 0 →
    coordinateWord (wordTable (vectorCode x))
      (if secondOrbit (vectorCode x) then secondVector else firstVector) = x := by
  decide +kernel

theorem evenAction_two_nonzero_orbits :
    ∃ r s : hexacode, r ≠ 0 ∧ s ≠ 0 ∧
      ∀ v : hexacode, v ≠ 0 →
        (∃ g : HexEvenAutomorphisms, evenAction g r = v) ∨
        (∃ g : HexEvenAutomorphisms, evenAction g s = v) := by
  let r := binaryCoordinates.symm firstVector
  let s := binaryCoordinates.symm secondVector
  have hr : r ≠ 0 := by
    intro h
    have := congrArg binaryCoordinates h
    change binaryCoordinates (binaryCoordinates.symm firstVector) = binaryCoordinates 0 at this
    rw [binaryCoordinates.apply_symm_apply,map_zero] at this
    exact (by decide : firstVector ≠ 0) this
  have hs : s ≠ 0 := by
    intro h
    have := congrArg binaryCoordinates h
    change binaryCoordinates (binaryCoordinates.symm secondVector) = binaryCoordinates 0 at this
    rw [binaryCoordinates.apply_symm_apply,map_zero] at this
    exact (by decide : secondVector ≠ 0) this
  refine ⟨r,s,hr,hs,?_⟩
  intro v hv
  have hx : binaryCoordinates v ≠ 0 := by simpa using hv
  have hc := coordinate_cover (binaryCoordinates v) hx
  cases hb : secondOrbit (vectorCode (binaryCoordinates v))
  · left
    refine ⟨groupWord (wordTable (vectorCode (binaryCoordinates v))),?_⟩
    apply binaryCoordinates.injective
    rw [word_coordinates,show binaryCoordinates r = firstVector from binaryCoordinates.apply_symm_apply _]
    simpa only [hb,Bool.false_eq_true,ite_false] using hc
  · right
    refine ⟨groupWord (wordTable (vectorCode (binaryCoordinates v))),?_⟩
    apply binaryCoordinates.injective
    rw [word_coordinates,show binaryCoordinates s = secondVector from binaryCoordinates.apply_symm_apply _]
    simpa only [hb,ite_true] using hc

theorem evenAction_orbitCardSeparates : OrbitCardSeparates evenAction := by
  obtain ⟨r,s,hr,hs,hcover⟩ := evenAction_two_nonzero_orbits
  exact OrbitCardSeparates.of_two_nonzero_orbits evenAction
    (by rw [hexacode_card]; decide) r s hr hs hcover

end Representation.Hexacode
