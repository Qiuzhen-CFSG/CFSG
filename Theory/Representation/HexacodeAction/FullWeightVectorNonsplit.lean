module

public import Theory.Representation.HexacodeAction.FullWeightVectorStabilizer
public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# Full commutator generation at a full-weight hexacode vector

Two words in the existing even generators fix the full-weight word with
field coordinates `(omega,1,1)`. Three columns of their displacement maps
are a basis of the actual three-dimensional field space. An explicit
coordinate identity therefore writes every codeword as the sum of two
displacements by elements fixing that word. Transitivity on the full-weight
orbit transports the identity to every full-weight vector.

Consequently the vector stabilizer generates the whole binary module by
commutators. Its fixed field point has no invariant binary complement.
This proves the nonsplitting calculation in Aschbacher--Smith 12.7.4(2),
printed pp.839--840, on the whole original hexacode carrier. The code and
operators retain their ATLAS attribution; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open SixDimensional.EvenImage BinaryOffender

private def coordinateStep (b : Bool) (x : Fin 3 → F) : Fin 3 → F :=
  if b then ![x 2, omega * x 0, omega ^ 2 * x 1]
  else ![x 0 + x 1 + x 2, x 0, x 1]

private def coordinateWord (l : List Bool) (x : Fin 3 → F) : Fin 3 → F :=
  l.foldr coordinateStep x

private def groupWord (l : List Bool) : HexEvenAutomorphisms :=
  (l.map fun b => if b then generatorB else generatorA).prod

private theorem word_coordinates (l : List Bool) (v : hexacode) :
    fieldCoordinates (evenAction (groupWord l) v) = coordinateWord l (fieldCoordinates v) := by
  induction l with
  | nil => simp [groupWord, coordinateWord]
  | cons b l ih =>
    simp only [groupWord, List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply]
    change fieldCoordinates (evenAction (if b then generatorB else generatorA)
      (evenAction (groupWord l) v)) = _
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [show fieldCoordinates (evenAction generatorA (evenAction (groupWord l) v)) =
        ![fieldCoordinates (evenAction (groupWord l) v) 0 +
          fieldCoordinates (evenAction (groupWord l) v) 1 +
          fieldCoordinates (evenAction (groupWord l) v) 2,
          fieldCoordinates (evenAction (groupWord l) v) 0,
          fieldCoordinates (evenAction (groupWord l) v) 1] from generatorA_coordinates _]
      rw [ih]
      rfl
    · simp only [ite_true]
      rw [show fieldCoordinates (evenAction generatorB (evenAction (groupWord l) v)) =
        ![fieldCoordinates (evenAction (groupWord l) v) 2,
          omega * fieldCoordinates (evenAction (groupWord l) v) 0,
          omega ^ 2 * fieldCoordinates (evenAction (groupWord l) v) 1]
        from generatorB_coordinates _]
      rw [ih]
      rfl

private def firstWord : List Bool := [false,false,true,true,false]
private def secondWord : List Bool := [true,false,true,false,false,false]
private def seed : hexacode := ⟨systematicEncoder ![b,a,a], systematic_mem _⟩

private theorem seed_coordinates : fieldCoordinates seed = ![omega,1,1] := by
  funext i
  change orientedLetter (firstThree i) (seed.val (firstThree i)) = _
  revert i
  decide

private theorem seed_weight : hammingNorm seed.val = 6 := by decide

private theorem seed_nonzero : seed ≠ 0 := by
  intro h
  have hh := seed_weight
  simp [h] at hh

private theorem words_fix_seed :
    evenAction (groupWord firstWord) seed = seed ∧
      evenAction (groupWord secondWord) seed = seed := by
  constructor <;> apply fieldCoordinates.injective <;>
    rw [word_coordinates, seed_coordinates] <;> decide

private def firstInput (x : Fin 3 → F) : Fin 3 → F :=
  ![x 0 + omega ^ 2 * x 1, omega ^ 2 * x 1 + omega * x 2, 0]

private def secondInput (x : Fin 3 → F) : Fin 3 → F :=
  ![x 0 + omega ^ 2 * x 1 + omega * x 2, 0, 0]

private theorem coordinate_decomposition : ∀ x : Fin 3 → F,
    x = (coordinateWord firstWord (firstInput x) - firstInput x) +
      (coordinateWord secondWord (secondInput x) - secondInput x) := by
  decide +kernel

private theorem seed_decomposition (w : hexacode) :
    ∃ x y : hexacode,
      w = (evenAction (groupWord firstWord) x - x) +
        (evenAction (groupWord secondWord) y - y) := by
  refine ⟨fieldCoordinates.symm (firstInput (fieldCoordinates w)),
    fieldCoordinates.symm (secondInput (fieldCoordinates w)), ?_⟩
  apply fieldCoordinates.injective
  rw [map_add, map_sub, map_sub, word_coordinates, word_coordinates,
    fieldCoordinates.apply_symm_apply, fieldCoordinates.apply_symm_apply]
  exact coordinate_decomposition _

private theorem full_weight_decomposition (v : hexacode)
    (hv : hammingNorm v.val = 6) (w : hexacode) :
    ∃ g h : HexEvenAutomorphisms, evenAction g v = v ∧ evenAction h v = v ∧
      ∃ x y : hexacode, w = (evenAction g x - x) + (evenAction h y - y) := by
  have hv_mem : v ∈ Set.range (fun g : HexEvenAutomorphisms => evenAction g seed) := by
    rw [evenAction_orbit_eq_weight seed seed_nonzero]
    exact hv.trans seed_weight.symm
  obtain ⟨k, rfl⟩ := hv_mem
  obtain ⟨x,y,hxy⟩ := seed_decomposition (evenAction k⁻¹ w)
  have hconj (g : HexEvenAutomorphisms) (u : hexacode) :
      evenAction (k*g*k⁻¹) (evenAction k u) = evenAction k (evenAction g u) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  refine ⟨k*groupWord firstWord*k⁻¹, k*groupWord secondWord*k⁻¹, ?_, ?_,
    evenAction k x, evenAction k y, ?_⟩
  · rw [hconj, words_fix_seed.1]
  · rw [hconj, words_fix_seed.2]
  · have he := congrArg (evenAction k) hxy
    rw [map_add, map_sub, map_sub] at he
    rw [hconj, hconj]
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] using he

/-- The stabilizer of an actual full-weight vector generates the entire
six-dimensional binary module by its action differences. -/
theorem fullWeightVectorStabilizer_commutator (v : hexacode)
    (hv : hammingNorm v.val = 6) :
    subspaceCommutator evenAction ⊤ (fullWeightVectorStabilizer v) = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨g,h,hg,hh,x,y,rfl⟩ := full_weight_decomposition v hv w
  exact Submodule.add_mem _
    (Submodule.subset_span ⟨g,hg,x,Submodule.mem_top,rfl⟩)
    (Submodule.subset_span ⟨h,hh,y,Submodule.mem_top,rfl⟩)

/-- The actual scalar point is fixed pointwise by its vector stabilizer. -/
theorem fullWeightVectorStabilizer_fixes_point (v : hexacode) :
    ((Submodule.span F {v}).restrictScalars Bit) ≤
      fixedSpace evenAction (fullWeightVectorStabilizer v) := by
  intro w hw g
  obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hw
  change evenFieldAction g.val (r • v) = r • v
  rw [map_smul]
  exact congrArg (fun z => r • z) g.property

/-- No invariant binary complement to the same field point exists inside
the whole hexacode module. -/
theorem fullWeightVectorStabilizer_nonsplit (v : hexacode)
    (hv : hammingNorm v.val = 6) (W : Submodule Bit hexacode)
    (hW : fullWeightVectorStabilizer v ≤ subspaceStabilizer evenAction W) :
    ¬ IsCompl ((Submodule.span F {v}).restrictScalars Bit) W := by
  intro hc
  have hm := subspaceCommutator_le_of_le_sup_fixedSpace evenAction hW
    (show (⊤ : Submodule Bit hexacode) ≤
      W ⊔ fixedSpace evenAction (fullWeightVectorStabilizer v) from by
      calc
        ⊤ = W ⊔ (Submodule.span F {v}).restrictScalars Bit := hc.symm.sup_eq_top.symm
        _ ≤ W ⊔ fixedSpace evenAction (fullWeightVectorStabilizer v) :=
          sup_le_sup_left (fullWeightVectorStabilizer_fixes_point v) W)
  rw [fullWeightVectorStabilizer_commutator v hv] at hm
  have htop : W = ⊤ := top_unique hm
  have hpoint := hc.inf_eq_bot
  rw [htop, inf_top_eq] at hpoint
  have hzero : v = 0 := by
    have hh : v ∈ (Submodule.span F {v}).restrictScalars Bit :=
      Submodule.mem_span_singleton_self v
    rwa [hpoint, Submodule.mem_bot] at hh
  simp [hzero] at hv

end Representation.Hexacode
