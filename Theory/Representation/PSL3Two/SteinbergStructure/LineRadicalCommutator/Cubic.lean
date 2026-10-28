module

public import Theory.Representation.PSL3Two.SteinbergStructure.LineRadicalCommutator
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore

/-!
# A fixed-free cubic on the actual Steinberg line quotient

The upper-left cubic block sends the bottom-row coordinates (u,v) of a
trace-zero matrix to (u+v,u). Its displacement vanishes precisely when
both coordinates vanish. Thus its action on the quotient by the line
radical commutator has no nonzero fixed point. Conjugation preserves this
statement with the actual line radical and original Steinberg action.

Source: Aschbacher–Smith, J.4.4(2), printed p.441.
-/

public section
open Matrix Representation Representation.BinaryOffender
open BinaryLinearThree.IrreducibleCatalogue
namespace BinaryLinearThree.SteinbergStructure.LineRadicalCommutator
noncomputable section

def lineCubic : Group := ⟨!![0,1,0;1,1,0;0,0,1],by decide⟩

theorem lineCubic_mem : lineCubic∈Matrix.PSL3Two.lineParabolicSL := by
  rw [Matrix.PSL3Two.mem_lineParabolicSL_iff]
  exact ⟨rfl,rfl⟩

theorem lineCubic_order : orderOf lineCubic=3 :=
  orderOf_eq_prime (by decide) (by decide)

private theorem bottom_action (v : Steinberg) :
    coordinates (S lineCubic v) 4=coordinates v 4+coordinates v 5 ∧
      coordinates (S lineCubic v) 5=coordinates v 4 := by
  obtain ⟨w,rfl⟩ := coordinates.symm.surjective v
  rw [LinearEquiv.apply_symm_apply]
  have he : coordinates (S lineCubic (coordinates.symm w))=
      readMatrix (lineCubic.val * matrixOf w * lineCubic.val.adjugate) := by
    change readMatrix (LinearMap.toMatrix'
      (lineCubic.val.toLin' ∘ₗ (matrixOf w).toLin' ∘ₗ lineCubic.val.adjugate.toLin'))=_
    rw [← Matrix.toLin'_mul,← Matrix.toLin'_mul,LinearMap.toMatrix'_toLin']
    exact congrArg readMatrix (Matrix.mul_assoc _ _ _).symm
  rw [he]
  simp [lineCubic,readMatrix,matrixOf,Matrix.mul_apply,Fin.sum_univ_three,
    Matrix.adjugate_fin_three]

theorem lineCubic_fixed_mod_commutator (v : Steinberg)
    (h : S lineCubic v-v ∈ subspaceCommutator S ⊤ R) :
    v∈subspaceCommutator S ⊤ R := by
  rw [mem_commutator_iff] at h ⊢
  have he := bottom_action v
  have h4 : coordinates (S lineCubic v-v) 4=coordinates (S lineCubic v) 4-coordinates v 4 :=
    congrFun (coordinates.map_sub _ _) 4
  have h5 : coordinates (S lineCubic v-v) 5=coordinates (S lineCubic v) 5-coordinates v 5 :=
    congrFun (coordinates.map_sub _ _) 5
  rw [h4,h5,he.1,he.2] at h
  have hz : coordinates v 5=0 := by simpa only [add_sub_cancel_left] using h.1
  exact ⟨by simpa only [hz,sub_zero] using h.2,hz⟩

theorem conjugate_lineCubic_fixed_mod_commutator (g : Group) (v : Steinberg)
    (h : S (g*lineCubic*g⁻¹) v-v ∈
      subspaceCommutator S ⊤ (R.map (MulAut.conj g).toMonoidHom)) :
    v∈subspaceCommutator S ⊤ (R.map (MulAut.conj g).toMonoidHom) := by
  have hm := Submodule.mem_map_of_mem (f := S g⁻¹) h
  rw [conjugate_commutator] at hm
  have hsub : S g⁻¹ (S (g*lineCubic*g⁻¹) v-v)=S g⁻¹ (S (g*lineCubic*g⁻¹) v)-S g⁻¹ v := (S g⁻¹).map_sub _ _
  rw [hsub] at hm
  have he : S g⁻¹ (S (g*lineCubic*g⁻¹) v)=S lineCubic (S g⁻¹ v) := by
    simp only [map_mul,Module.End.mul_apply,Representation.inv_self_apply]
  rw [he] at hm
  have hv := lineCubic_fixed_mod_commutator _ hm
  rw [← conjugate_commutator g] at hv
  obtain ⟨w,hw,he⟩ := hv
  exact ((S.apply_bijective g⁻¹).injective he) ▸ hw

end
end BinaryLinearThree.SteinbergStructure.LineRadicalCommutator
