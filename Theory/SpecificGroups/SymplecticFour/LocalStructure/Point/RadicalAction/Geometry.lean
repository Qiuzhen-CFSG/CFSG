module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Theory.SpecificGroups.SymplecticFour.RootHyperplane
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup

/-!
# Natural displacement and hyperplane fixation of the point radical

The literal radical matrices fix precisely the standard point. Nondegeneracy
of the symplectic form identifies their displacement span with its perpendicular
hyperplane. Long root zero moves precisely the point, and the field-sized
root-fixer theorem identifies it with the entire pointwise hyperplane fixer.
We also prove displacement and fixer transport by the actual symplectic
matrix conjugation and the corresponding natural linear map.

Source: Aschbacher--Smith 11.5.7, assertion (!) and the next paragraph,
refs/quasithin.pdf, printed pp.782--783.
-/

public noncomputable section
open Subgroup Matrix Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.PointRadicalAction
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
/-- The full long root has exactly the standard point as natural displacement. -/
theorem root_displacement : displacementSpace (RootSubgroup.group (F := F) 0) = point F := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    obtain ⟨z, hz⟩ := (RootSubgroup.mem_group_iff 0 g.val).mp g.property
    change g.val • v - v ∈ point F
    rw [← hz]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨z * v (.inr 0), ?_⟩
    ext i
    fin_cases i <;> simp [rootElement, rootMatrix, Matrix.mulVec,
      dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single, e]
  · apply Submodule.span_le.mpr
    rintro v (rfl : v = e (F := F) 0)
    have he : rootElement (K := F) 0 1 • (Pi.single (.inr 0) (1 : F) : Vector F) -
        Pi.single (.inr 0) 1 = e 0 := by
      ext i
      fin_cases i <;> simp [rootElement, rootMatrix,
        Matrix.mulVec_single, Matrix.single, e]
    rw [← he]
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp (RootSubgroup.group (F := F) 0).subtype)
      ⟨rootElement 0 1, (RootSubgroup.mem_group_iff 0 _).mpr ⟨1, rfl⟩⟩ _

/-- The embedded point radical fixes exactly its defining point. -/
theorem radical_fixedSpace :
    TwoLocalCover.fixedSpace ((pointRadical (F := F)).map pointLocal.subtype) = point F := by
  ext x
  constructor
  · intro h
    have hm (u v z : F) : (pointRadicalElement u v z).val ∈
        (pointRadical (F := F)).map pointLocal.subtype :=
      Subgroup.mem_map_of_mem _ (pointRadicalElement_mem u v z)
    have h₀ := congrFun (h _ (hm 0 0 1)) (.inl 0)
    have h₁ := congrFun (h _ (hm 1 0 0)) (.inl 0)
    have h₂ := congrFun (h _ (hm 0 1 0)) (.inl 0)
    simp [pointRadicalElement, pointRadicalMatrix, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] at h₀ h₁ h₂
    exact (mem_point_iff x).mpr ⟨h₂, by intro i; fin_cases i <;> assumption⟩
  · intro hx q hq
    obtain ⟨q, _, rfl⟩ := hq
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change toLinear q.val (a • e 0) = a • e 0
    rw [map_smul]
    exact congrArg (a • ·) ((mem_pointLocal_iff_fixed q.val).mp q.property)

/-- The embedded point radical moves exactly the perpendicular hyperplane. -/
theorem radical_displacement :
    displacementSpace ((pointRadical (F := F)).map pointLocal.subtype) =
      (form F).orthogonal (point F) := by
  rw [← radical_fixedSpace, ← orthogonal_displacementSpace]
  exact (LinearMap.BilinForm.orthogonal_orthogonal
    TwoLocalCover.form_nondegenerate TwoLocalCover.form_alternating.isRefl _).symm

omit [CharP F 2] in
/-- The entire pointwise hyperplane fixer in Sp is the literal long root zero. -/
theorem hyperplane_fixer [Finite F] :
    fixingSubgroup (Sp F) ((form F).orthogonal (point F) : Set (Vector F)) =
      RootSubgroup.group 0 := by
  rw [← root_displacement, orthogonal_displacementSpace]
  exact root_fixedSpace_fixer_eq _ (by rw [root_displacement, finrank_point])
    (RootSubgroup.card 0)

omit [CharP F 2] in
/-- Natural displacement transports through genuine symplectic conjugation. -/
theorem displacement_conjugate (A : Subgroup (Sp F)) (g : Sp F) :
    displacementSpace (A.map (MulAut.conj g).toMonoidHom) =
      (displacementSpace A).map (toLinear g).toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    obtain ⟨b, hb, he⟩ := a.property
    change a.val • v - v ∈ _
    rw [← he]
    refine ⟨b • (g⁻¹ • v) - g⁻¹ • v,
      Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp A.subtype) ⟨b, hb⟩ _, ?_⟩
    change toLinear g (_ - _) = (g * b * g⁻¹) • v - v
    rw [map_sub]
    simp only [toLinear_apply, mul_smul, smul_inv_smul]
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    apply Submodule.mem_comap.mpr
    change (toLinear g).toLinearMap (a.val • v - v) ∈ _
    rw [map_sub]
    have he : (g * a.val * g⁻¹) • (g • v) - g • v =
        g • (a.val • v) - g • v := by simp [mul_smul]
    change g • (a.val • v) - g • v ∈ _
    rw [← he]
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp (A.map (MulAut.conj g).toMonoidHom).subtype)
      ⟨_, mem_map_of_mem _ a.property⟩ _

omit [CharP F 2] in
/-- The pointwise fixer transports through the same natural symplectic map. -/
theorem fixer_conjugate (W : Submodule F (Vector F)) (g : Sp F) :
    fixingSubgroup (Sp F) (W.map (toLinear g).toLinearMap : Set (Vector F)) =
      (fixingSubgroup (Sp F) (W : Set (Vector F))).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · intro a ha
    refine ⟨g⁻¹ * a * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    apply (mem_fixingSubgroup_iff _).mpr
    intro v hv
    have h := (mem_fixingSubgroup_iff _).mp ha (g • v) ⟨v, hv, rfl⟩
    change (g⁻¹ * a * g) • v = v
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · rintro _ ⟨a, ha, rfl⟩
    apply (mem_fixingSubgroup_iff _).mpr
    rintro _ ⟨v, hv, rfl⟩
    change (g * a * g⁻¹) • (g • v) = g • v
    simp only [mul_smul, inv_smul_smul, (mem_fixingSubgroup_iff _).mp ha v hv]

end Theory.SpecificGroups.SymplecticFour.PointRadicalAction
