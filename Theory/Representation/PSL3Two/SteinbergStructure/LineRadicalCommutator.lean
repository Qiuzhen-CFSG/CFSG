module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.FinCases

/-!
# The Steinberg commutator of a line radical

In trace-zero matrix coordinates, the line radical fixes the two entries in
the last row outside the diagonal. Its commutator space is exactly their
common kernel. Six explicit displacements give the reverse containment,
and dropping those two coordinates identifies the space with F₂⁶.
Conjugation transports this calculation to every conjugate line radical.

Source: Aschbacher–Smith, J.4.3(1), printed p.441.
-/

public section
open Matrix Representation
open BinaryLinearThree.IrreducibleCatalogue Representation.BinaryOffender
namespace BinaryLinearThree.SteinbergStructure.LineRadicalCommutator
noncomputable section

private def act (g : Group) (v : Eight) : Eight :=
  readMatrix (g.val * matrixOf v * g.val.adjugate)

private theorem coordinates_sub (u v : Steinberg) :
    coordinates (u - v) = coordinates u - coordinates v := coordinates.map_sub u v

private theorem coordinates_action (g : Group) (v : Steinberg) :
    coordinates (S g v) = act g (coordinates v) := by
  obtain ⟨w, rfl⟩ := coordinates.symm.surjective v
  rw [LinearEquiv.apply_symm_apply]
  change readMatrix (LinearMap.toMatrix' (W g ∘ₗ (matrixOf w).toLin' ∘ₗ W g⁻¹)) = _
  change readMatrix (LinearMap.toMatrix'
    (g.val.toLin' ∘ₗ (matrixOf w).toLin' ∘ₗ g.val.adjugate.toLin')) = _
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, LinearMap.toMatrix'_toLin']
  exact congrArg readMatrix (Matrix.mul_assoc _ _ _).symm

private theorem shear_last (c : Multiplicative (ZMod 2 × ZMod 2)) (v : Eight) :
    act (BinaryLinearThree.shear c) v 4 = v 4 ∧
      act (BinaryLinearThree.shear c) v 5 = v 5 := by
  change readMatrix
      (!![1,0,c.toAdd.1;0,1,c.toAdd.2;0,0,1] * matrixOf v *
        (!![1,0,c.toAdd.1;0,1,c.toAdd.2;0,0,1]).adjugate) 4 = v 4 ∧
    readMatrix
      (!![1,0,c.toAdd.1;0,1,c.toAdd.2;0,0,1] * matrixOf v *
        (!![1,0,c.toAdd.1;0,1,c.toAdd.2;0,0,1]).adjugate) 5 = v 5
  simp [matrixOf, readMatrix, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.adjugate_fin_three]

private def basisIndex (i : Fin 6) : Fin 8 := ![0,1,2,3,6,7] i
private def actorPair (i : Fin 6) : ZMod 2 × ZMod 2 :=
  ![(1,0),(0,1),(0,1),(0,1),(1,0),(0,1)] i
private def seed (i : Fin 6) : Eight :=
  ![![0,0,0,0,0,1,0,0], ![1,0,0,0,0,0,0,0],
    ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,0,1,0],
    ![0,0,0,0,1,0,0,1], ![0,0,0,0,0,1,1,0]] i
private theorem basis_displacement (i : Fin 6) :
    act (BinaryLinearThree.shear (.ofAdd (actorPair i))) (seed i) - seed i =
      Pi.single (basisIndex i) 1 := by
  simp only [act, Matrix.adjugate_fin_three]
  fin_cases i <;> decide +kernel

def coordinateSpace : Submodule (ZMod 2) Eight where
  carrier := {v | v 4 = 0 ∧ v 5 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨by change a 4 + b 4 = 0; rw [ha.1,hb.1,add_zero],
      by change a 5 + b 5 = 0; rw [ha.2,hb.2,add_zero]⟩
  smul_mem' a v hv := by change _ * _ = 0 ∧ _ * _ = 0; simp [hv.1, hv.2]

def coordinateEquiv : coordinateSpace ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun v := ![v.val 0,v.val 1,v.val 2,v.val 3,v.val 6,v.val 7]
  invFun w := ⟨![w 0,w 1,w 2,w 3,0,0,w 4,w 5], by exact ⟨rfl,rfl⟩⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [v.property.1,v.property.2]
  right_inv w := by funext i; fin_cases i <;> rfl
  map_add' _ _ := by funext i; fin_cases i <;> rfl
  map_smul' _ _ := by funext i; fin_cases i <;> rfl

def lineSpace : Submodule (ZMod 2) Steinberg := coordinateSpace.comap coordinates.toLinearMap

private theorem commutator_le : subspaceCommutator S ⊤ R ≤ lineSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, ⟨c,rfl⟩, v, _, rfl⟩
  change coordinates (S (BinaryLinearThree.shear c) v - v) 4 = 0 ∧
    coordinates (S (BinaryLinearThree.shear c) v - v) 5 = 0
  rw [coordinates_sub, coordinates_action]
  simpa only [Pi.sub_apply, (shear_last c (coordinates v)).1,
    (shear_last c (coordinates v)).2, sub_self] using (And.intro rfl rfl :
      (0 : ZMod 2) = 0 ∧ (0 : ZMod 2) = 0)

private theorem le_commutator : lineSpace ≤ subspaceCommutator S ⊤ R := by
  have hb (i : Fin 6) : coordinates.symm (Pi.single (basisIndex i) 1) ∈
      subspaceCommutator S ⊤ R := by
    have hd : S (BinaryLinearThree.shear (.ofAdd (actorPair i)))
        (coordinates.symm (seed i)) - coordinates.symm (seed i) =
        coordinates.symm (Pi.single (basisIndex i) 1) := by
      apply coordinates.injective
      rw [coordinates_sub, coordinates_action, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      exact basis_displacement i
    exact Submodule.subset_span ⟨_, ⟨.ofAdd (actorPair i),rfl⟩,
      coordinates.symm (seed i), Submodule.mem_top, hd.symm⟩
  intro v hv
  have hcoords : coordinates v 4 = 0 ∧ coordinates v 5 = 0 := hv
  have hb8 (i : Fin 8) : (coordinates v i) • coordinates.symm (Pi.single i 1) ∈
      subspaceCommutator S ⊤ R := by
    fin_cases i
    · exact Submodule.smul_mem _ _ (hb 0)
    · exact Submodule.smul_mem _ _ (hb 1)
    · exact Submodule.smul_mem _ _ (hb 2)
    · exact Submodule.smul_mem _ _ (hb 3)
    · change (coordinates v 4) • _ ∈ _
      rw [hcoords.1,zero_smul]; exact Submodule.zero_mem _
    · change (coordinates v 5) • _ ∈ _
      rw [hcoords.2,zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (hb 4)
    · exact Submodule.smul_mem _ _ (hb 5)
  have he : v = ∑ i, (coordinates v i) • coordinates.symm (Pi.single i 1) := by
    simpa only [LinearEquiv.symm_apply_apply, map_sum, map_smul] using
      congrArg coordinates.symm (pi_eq_sum_univ' (coordinates v))
  rw [he]
  exact Submodule.sum_mem _ fun i _ => hb8 i

theorem commutator_eq : subspaceCommutator S ⊤ R = lineSpace :=
  le_antisymm commutator_le le_commutator

def lineCoordinates : lineSpace ≃ₗ[ZMod 2] coordinateSpace where
  toFun v := ⟨coordinates v, v.property⟩
  invFun v := ⟨coordinates.symm v, by
    change coordinates (coordinates.symm v) ∈ coordinateSpace
    simpa only [LinearEquiv.apply_symm_apply] using v.property⟩
  left_inv v := Subtype.ext (coordinates.symm_apply_apply v)
  right_inv v := Subtype.ext (coordinates.apply_symm_apply v)
  map_add' u v := Subtype.ext (coordinates.map_add u v)
  map_smul' a v := Subtype.ext (coordinates.map_smul a v)

theorem finrank_commutator : Module.finrank (ZMod 2) (subspaceCommutator S ⊤ R) = 6 := by
  rw [commutator_eq]
  simpa using (lineCoordinates.trans coordinateEquiv).finrank_eq

theorem mem_commutator_iff (v : Steinberg) :
    v ∈ subspaceCommutator S ⊤ R ↔ coordinates v 4 = 0 ∧ coordinates v 5 = 0 := by
  rw [commutator_eq]
  rfl

theorem conjugate_commutator (g : Group) :
    (subspaceCommutator S ⊤ (R.map (MulAut.conj g).toMonoidHom)).map (S g⁻¹) =
      subspaceCommutator S ⊤ R := by
  have he (a : Group) (v : Steinberg) :
      S a (S g⁻¹ v) = S g⁻¹ (S ((MulAut.conj g) a) v) := by
    simp only [MulAut.conj_apply, map_mul, Module.End.mul_apply,
      Representation.inv_self_apply]
  have ht := subspaceCommutator_map_embedding S S (MulAut.conj g).toMonoidHom
    (S g⁻¹) he R ⊤
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr (S.apply_bijective g⁻¹).surjective] at ht
  exact ht.symm

theorem finrank_conjugate_commutator (g : Group) :
    Module.finrank (ZMod 2) (subspaceCommutator S ⊤
      (R.map (MulAut.conj g).toMonoidHom)) = 6 := by
  let e := LinearEquiv.ofBijective (S g⁻¹) (S.apply_bijective g⁻¹)
  have h := e.finrank_map_eq
    (subspaceCommutator S ⊤ (R.map (MulAut.conj g).toMonoidHom))
  change Module.finrank (ZMod 2)
    ((subspaceCommutator S ⊤ (R.map (MulAut.conj g).toMonoidHom)).map (S g⁻¹)) = _ at h
  rw [conjugate_commutator] at h
  exact h.symm.trans finrank_commutator

theorem card_conjugate_commutator (g : Group) :
    Nat.card (subspaceCommutator S ⊤ (R.map (MulAut.conj g).toMonoidHom)) = 64 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    finrank_conjugate_commutator]
  rfl
end
end BinaryLinearThree.SteinbergStructure.LineRadicalCommutator
