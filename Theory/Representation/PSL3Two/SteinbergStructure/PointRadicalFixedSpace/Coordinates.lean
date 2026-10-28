module

public import Theory.Representation.PSL3Two.SteinbergStructure.LocalActions
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
import Mathlib.Tactic.LinearCombination
/-!
# Coordinates of the Steinberg fixed plane of a point radical

The two elementary translations force six of the eight adjoint coordinates
to vanish. Conversely every translation fixes the remaining upper row. This
identifies the fixed space as a plane of order four. Its three nonzero vectors
are parabolic translates of the marked Sylow-fixed vector E₀₂.

Every such endomorphism has image in the marked point, and every nonzero one
maps some vector onto that point. These are the model facts used to prove that
distinct conjugate fixed planes intersect trivially.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.3(8,9), printed p.433 (PDF p.444), using H.6.3(4).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Matrix.PSL3Two
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue
namespace BinaryLinearThree.SteinbergStructure.PointRadicalFixedSpace
noncomputable section
private def act (g : Group) (v : Eight) : Eight :=
  readMatrix (g.val * matrixOf v * g.val.adjugate)
private theorem coordinates_action (g : Group) (v : Steinberg) :
    coordinates (S g v) = act g (coordinates v) := by
  have hv : (matrixOf (coordinates v)).toLin' = v.val :=
    congrArg Subtype.val (coordinates.symm_apply_apply v)
  change readMatrix (LinearMap.toMatrix' (W g ∘ₗ v.val ∘ₗ W g⁻¹)) = _
  rw [← hv]
  change readMatrix (LinearMap.toMatrix'
    (g.val.toLin' ∘ₗ (matrixOf (coordinates v)).toLin' ∘ₗ g.val.adjugate.toLin')) = _
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, LinearMap.toMatrix'_toLin']
  exact congrArg readMatrix (Matrix.mul_assoc _ _ _).symm
private def row (a b : ZMod 2) : Eight := ![a,b,0,0,0,0,0,0]
private def upper02 : Group := ⟨!![1,0,1;0,1,0;0,0,1], by decide⟩
private theorem row_generators : IrreducibleCatalogue.shear ∈ MarkedAutomorphisms.pointV ∧
    upper02 ∈ MarkedAutomorphisms.pointV := by decide
private theorem fixed_lower (v : Eight) (hs : act IrreducibleCatalogue.shear v = v)
    (ht : act upper02 v = v) : v = row (v 0) (v 1) := by
  have h0 := congrFun hs 0
  have h1 := congrFun hs 1
  have h5 := congrFun hs 5
  have h6 := congrFun hs 6
  have k0 := congrFun ht 0
  have k1 := congrFun ht 1
  simp [act,IrreducibleCatalogue.shear,upper02,readMatrix,matrixOf,
    Matrix.mul_apply,Fin.sum_univ_three,Matrix.adjugate_fin_three] at h0 h1 h5 h6 k0 k1
  have hz2 : v 2 = 0 := h6
  have hz3 : v 3 = 0 := h1
  have hz4 : v 4 = 0 := h5
  have hz5 : v 5 = 0 := k0
  have hz7 : v 7 = 0 := by
    linear_combination (norm := ring_nf) k1 - hz4
    simp [show (2 : ZMod 2) = 0 by decide]
  have hz6 : v 6 = 0 := by linear_combination h0 - hz2 - hz7
  funext i
  fin_cases i <;> simp [row,hz2,hz3,hz4,hz5,hz6,hz7]
private theorem fixed_upper (g : Group) (hg : g ∈ MarkedAutomorphisms.pointV)
    (a b : ZMod 2) : act g (row a b) = row a b := by
  have hm : g.val = !![1,g.val 0 1,g.val 0 2;0,1,0;0,0,1] := by
    change g.val 0 0 = 1 ∧ g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧
      g.val 1 1 = 1 ∧ g.val 1 2 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1 at hg
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  unfold act
  rw [hm]
  funext i
  fin_cases i <;> simp [readMatrix,matrixOf,row,Matrix.mul_apply,
    Fin.sum_univ_three,Matrix.adjugate_fin_three]
/-- The fixed endomorphisms of the point radical have only an upper row. -/
private theorem mem_fixed_iff (v : Steinberg) :
    v ∈ fixedSpace S MarkedAutomorphisms.pointV ↔
      coordinates v = row (coordinates v 0) (coordinates v 1) := by
  constructor
  · intro h
    apply fixed_lower
    · rw [← coordinates_action]
      exact congrArg coordinates (h ⟨IrreducibleCatalogue.shear,row_generators.1⟩)
    · rw [← coordinates_action]
      exact congrArg coordinates (h ⟨upper02,row_generators.2⟩)
  · intro h g
    change S g.val v = v
    apply coordinates.injective
    rw [coordinates_action, h]
    exact fixed_upper g g.property _ _
/-- The point radical fixes exactly four vectors in the actual Steinberg module. -/
theorem card_fixed : Nat.card (fixedSpace S MarkedAutomorphisms.pointV) = 4 := by
  let f : fixedSpace S MarkedAutomorphisms.pointV → ZMod 2 × ZMod 2 :=
    fun v => (coordinates v.val 0, coordinates v.val 1)
  have hi : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    apply coordinates.injective
    have h0 : coordinates u.val 0 = coordinates v.val 0 := congrArg Prod.fst h
    have h1 : coordinates u.val 1 = coordinates v.val 1 := congrArg Prod.snd h
    exact ((mem_fixed_iff u.val).mp u.property).trans
      ((congrArg₂ row h0 h1).trans ((mem_fixed_iff v.val).mp v.property).symm)
  have hs : Function.Surjective f := by
    intro x
    have hm : coordinates.symm (row x.1 x.2) ∈ fixedSpace S MarkedAutomorphisms.pointV := by
      apply (mem_fixed_iff _).mpr
      rw [LinearEquiv.apply_symm_apply]
      rfl
    refine ⟨⟨coordinates.symm (row x.1 x.2),hm⟩, ?_⟩
    change (coordinates (coordinates.symm (row x.1 x.2)) 0,
      coordinates (coordinates.symm (row x.1 x.2)) 1) = x
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.eta x
  have hc : Nat.card (ZMod 2 × ZMod 2) = 4 := by rw [Nat.card_prod,Nat.card_zmod]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).trans hc
private def orbitActor (i : Fin 3) : Group :=
  ![1, ⟨!![1,0,0;0,0,1;0,1,0], by decide⟩,
    ⟨!![1,0,0;0,1,0;0,1,1], by decide⟩] i
private theorem orbitActor_mem (i : Fin 3) : orbitActor i ∈ pointParabolicSL := by
  fin_cases i <;> decide
private theorem row_orbit : ∀ a b : ZMod 2, row a b ≠ 0 →
    ∃ i : Fin 3, act (orbitActor i) (Pi.single 1 1) = row a b := by decide +kernel
private theorem coordinate_orbit (v : Steinberg) (hv : v ∈ fixedSpace S MarkedAutomorphisms.pointV)
    (hn : v ≠ 0) : ∃ g ∈ pointParabolicSL, S g (coordinates.symm (Pi.single 1 1)) = v := by
  have he := (mem_fixed_iff v).mp hv
  have hz : row (coordinates v 0) (coordinates v 1) ≠ 0 := by
    rw [← he]; exact fun h => hn (coordinates.map_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := row_orbit _ _ hz
  refine ⟨orbitActor i, orbitActor_mem i, coordinates.injective ?_⟩
  rw [coordinates_action]
  change act (orbitActor i) (coordinates (coordinates.symm (Pi.single 1 1))) = coordinates v
  rw [LinearEquiv.apply_symm_apply]
  exact hi.trans he.symm
/-- The point parabolic is transitive on nonzero radical-fixed vectors. -/
theorem fixed_orbit (v w : Steinberg)
    (hv : v ∈ fixedSpace S MarkedAutomorphisms.pointV)
    (hw : w ∈ fixedSpace S MarkedAutomorphisms.pointV)
    (hnv : v ≠ 0) (hnw : w ≠ 0) :
    ∃ g ∈ pointParabolicSL, S g w = v := by
  obtain ⟨a,ha,hea⟩ := coordinate_orbit v hv hnv
  obtain ⟨b,hb,heb⟩ := coordinate_orbit w hw hnw
  refine ⟨a*b⁻¹, pointParabolicSL.mul_mem ha (pointParabolicSL.inv_mem hb), ?_⟩
  rw [← heb, map_mul, Module.End.mul_apply, Representation.inv_self_apply, hea]
private theorem matrix_coordinates (v : Steinberg) :
    (matrixOf (coordinates v)).toLin' = v.val := congrArg Subtype.val (coordinates.symm_apply_apply v)
private theorem row_preimage : ∀ a b : ZMod 2, row a b ≠ 0 →
    ∃ i : Fin 3, (matrixOf (row a b)).mulVec (Pi.single i 1) = ![1,0,0] := by
  decide +kernel
private theorem row_image (a b : ZMod 2) (x : Vector) :
    ((matrixOf (row a b)).toLin' x) 1 = 0 ∧ ((matrixOf (row a b)).toLin' x) 2 = 0 := by
  simp [Matrix.toLin'_apply,matrixOf,row,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
/-- Every radical-fixed endomorphism has image in the marked point. -/
theorem fixed_image (v : Steinberg) (hv : v ∈ fixedSpace S MarkedAutomorphisms.pointV)
    (x : Vector) : (v.val x) 1 = 0 ∧ (v.val x) 2 = 0 := by
  have he := (mem_fixed_iff v).mp hv
  have hm := matrix_coordinates v
  rw [he] at hm
  have hi := row_image (coordinates v 0) (coordinates v 1) x
  rw [hm] at hi
  exact hi
/-- A nonzero radical-fixed endomorphism has the marked point in its image. -/
theorem fixed_preimage (v : Steinberg) (hv : v ∈ fixedSpace S MarkedAutomorphisms.pointV)
    (hn : v ≠ 0) : ∃ x : Vector, v.val x = ![1,0,0] := by
  have he := (mem_fixed_iff v).mp hv
  have hz : row (coordinates v 0) (coordinates v 1) ≠ 0 := by
    rw [← he]
    exact fun h => hn (coordinates.map_eq_zero_iff.mp h)
  obtain ⟨i,hi⟩ := row_preimage _ _ hz
  refine ⟨Pi.single i 1, ?_⟩
  rw [← matrix_coordinates v,he]
  exact hi
end
end BinaryLinearThree.SteinbergStructure.PointRadicalFixedSpace
