module
public import Theory.SpecificGroups.SymplecticFour.PointMoverGeneration
public import Theory.SpecificGroups.SymplecticFour.LargeSylowGeneration
/-!
# A point radical and a large quadratic actor generate Sp₄

A plane actor of order greater than the field contains a shear with a nonzero
diagonal entry. The opposite point radical adjusts the image of its central
long root to the opposite root. These two roots and the point radical generate
Sp₄. Swapping the two coordinates handles either diagonal, and the quadratic
actor's displacement plane supplies its actual change of basis.

This retains every characteristic-two field degree. The full-kernel and
selected-path consumers are NonbinarySymplectic.CriticalReduction.PointLargeSelection
and PointLargePaths. Source: MS93 (5.5), printed pp.915--917, large-image
point-radical branch.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.PointLargeGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
private def lowerPoint : Subgroup (Sp F) :=
  ((wing false).map unipotent.subtype).map (MulAut.conj TwoConjugate.opposition).toMonoidHom
private def lowerAdjust (u w : F) : Sp F :=
  TwoConjugate.opposition * (element (w/u) u⁻¹ 0 0).val * TwoConjugate.opposition⁻¹
omit [Finite F] in
private theorem lowerAdjust_matrix (u w : F) :
    (lowerAdjust u w).val = fromBlocks !![1,0;w/u,1] 0 !![u⁻¹,0;0,0] !![1,w/u;0,1] := by
  change (TwoConjugate.opposition (F := F)).val * (element (w/u) u⁻¹ 0 0).val.val *
    (TwoConjugate.opposition⁻¹).val = _
  rw [TwoConjugate.opposition_inv,element_matrix]
  simp [TwoConjugate.opposition,Matrix.fromBlocks_multiply]
omit [Finite F] in
private theorem adjusted_matrix (u w v : F) (hu : u≠0) :
    (lowerAdjust u w * (element 0 u w v).val).val =
      fromBlocks !![1,0;w/u,1] !![u,w;0,w*w/u+v]
        !![u⁻¹,0;0,0] !![0,0;0,1] := by
  change (lowerAdjust u w).val * (element 0 u w v).val.val = _
  rw [lowerAdjust_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.fromBlocks,CharTwo.add_self_eq_zero,hu,div_eq_mul_inv,
      mul_assoc,mul_comm,mul_left_comm]
omit [Finite F] in
private theorem adjusted_long_root (u w v s : F) (hu : u≠0) :
    (lowerAdjust u w * (element 0 u w v).val) * rootElement 1 s *
      (lowerAdjust u w * (element 0 u w v).val)⁻¹ = rootElement 0 (u^2*s) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (lowerAdjust u w * (element 0 u w v).val).val * rootMatrix 1 s =
    rootMatrix 0 (u^2*s) * (lowerAdjust u w * (element 0 u w v).val).val
  rw [adjusted_matrix _ _ _ hu]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero,hu,
      pow_two,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
  field_simp
private theorem lowerPoint_root (s : F) : rootElement 1 s ∈ lowerPoint (F := F) := by
  refine ⟨rootElement 0 s,?_,(TwoConjugate.opposition_central_axes s).1⟩
  refine ⟨element 0 s 0 0,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
  simp [element,RootSubgroup.element_zero]
private theorem lowerPoint_long_root : lowerPoint (F := F) ⊔ RootSubgroup.group 0 = ⊤ := by
  have hh := congrArg (Subgroup.map (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom)
    (SelectedGeneration.point_wing_and_long_root (F := F))
  have hr : (RootSubgroup.group (F := F) 1).map (MulAut.conj TwoConjugate.opposition).toMonoidHom =
      RootSubgroup.group 0 := by
    have h10 (s : F) : TwoConjugate.opposition * rootElement 1 s *
        TwoConjugate.opposition⁻¹ = rootElement 0 s := by
      calc
        _ = TwoConjugate.opposition⁻¹ * rootElement 1 s * TwoConjugate.opposition := by
          rw [TwoConjugate.opposition_inv]
        _ = rootElement 0 s := by rw [←(TwoConjugate.opposition_central_axes s).1]; group
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨s,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hz
      change TwoConjugate.opposition * rootElement 1 s * TwoConjugate.opposition⁻¹ ∈ _
      rw [h10]
      exact subset_closure ⟨s,rfl⟩
    · intro hy
      obtain ⟨s,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hy
      exact ⟨rootElement 1 s,subset_closure ⟨s,rfl⟩,h10 s⟩
  rw [Subgroup.map_sup,hr,map_top_of_surjective _ (MulAut.conj _).surjective] at hh
  exact hh

private theorem lowerPoint_shear_generate (A : Subgroup (Sp F))
    {u w v : F} (hu : u≠0) (ha : (element 0 u w v).val ∈ A) :
    lowerPoint ⊔ A = ⊤ := by
  let H := lowerPoint ⊔ A
  have hk : lowerAdjust u w ∈ H := by
    apply (show lowerPoint ≤ H from le_sup_left)
    refine ⟨(element (w/u) u⁻¹ 0 0).val,?_,rfl⟩
    exact mem_map_of_mem _ ((element_mem_wing false _ _ _ _).mpr rfl)
  have hh : lowerAdjust u w * (element 0 u w v).val ∈ H :=
    H.mul_mem hk (mem_sup_right ha)
  have h0 (s : F) : rootElement 0 s ∈ H := by
    have hlong := H.mul_mem (H.mul_mem hh (mem_sup_left (lowerPoint_root (s/u^2)))) (H.inv_mem hh)
    rw [adjusted_long_root _ _ _ _ hu,mul_div_cancel₀ _ (pow_ne_zero _ hu)] at hlong
    exact hlong
  exact top_unique (lowerPoint_long_root (F := F) ▸
    sup_le (show lowerPoint ≤ H from le_sup_left)
      ((closure_le _).mpr (by rintro _ ⟨s,rfl⟩; exact h0 s)))

private def swapPairs : Sp F := rootElement 6 1 * rootElement 7 1 * rootElement 6 1
omit [Finite F] in
private theorem swapPairs_matrix : (swapPairs (F := F)).val =
    fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0] := by
  change rootMatrix 6 1 * rootMatrix 7 1 * rootMatrix 6 1 = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
omit [Finite F] in
private theorem swapPairs_shear (u w v : F) :
    swapPairs * (element 0 u w v).val * swapPairs⁻¹ = (element 0 v w u).val := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (swapPairs (F := F)).val * (element 0 u w v).val.val =
    (element 0 v w u).val.val * (swapPairs (F := F)).val
  rw [swapPairs_matrix,element_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks]

private theorem large_plane_nonzero_diagonal (A : Subgroup (Sp F))
    (hp : A ≤ (wing true).map unipotent.subtype) (hc : Nat.card F < Nat.card A) :
    ∃ u w v : F, (element 0 u w v).val ∈ A ∧ (u≠0 ∨ v≠0) := by
  by_contra! hn
  have hle : A ≤ RootSubgroup.group 4 := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hp hx
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
    have hb : b=0 := (element_mem_wing true _ _ _ _).mp hy
    subst b
    obtain ⟨rfl,rfl⟩ := hn u w v hx
    have he : (element (0:F) 0 w 0).val = rootElement 4 w := by
      simp [element,RootSubgroup.element_zero]
    change (element 0 0 w 0).val ∈ RootSubgroup.group 4
    rw [he]
    exact subset_closure ⟨w,rfl⟩
  have hh := card_le_of_le hle
  rw [RootSubgroup.card] at hh
  exact hc.not_ge hh

omit [CharP F 2] [Finite F] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

/-- Every large quadratic actor has a conjugate generating with the full
point radical, over the original field. No transvection inside the actor
or field-four restriction is assumed. -/
theorem exists_point_large_quadratic_generator
    (E A : Subgroup (Sp F))
    (hE : ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing false).map (unipotent (F := F)).subtype)
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hc : Nat.card F < Nat.card A) :
    ∃ g : Sp F, E.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨k,hk⟩ := hE
  obtain ⟨c,hcA⟩ := LargePlaneGeneration.large_quadratic_plane_coordinates A hq hc
  rw [SymplecticConjugatePair.planeRadical_eq_wing] at hcA
  obtain ⟨u,w,v,ha,hd⟩ := large_plane_nonzero_diagonal
    (A.map (MulAut.conj c).toMonoidHom) hcA
    (by rw [card_map_of_injective (MulAut.conj c).injective]; exact hc)
  obtain ⟨c',hgen⟩ : ∃ c' : Sp F, lowerPoint ⊔ A.map (MulAut.conj c').toMonoidHom = ⊤ := by
    rcases hd with hu | hv
    · exact ⟨c,lowerPoint_shear_generate _ hu ha⟩
    · refine ⟨swapPairs*c,?_⟩
      have hh := mem_map_of_mem (MulAut.conj (swapPairs (F := F))).toMonoidHom ha
      change swapPairs * (element 0 u w v).val * swapPairs⁻¹ ∈ _ at hh
      rw [swapPairs_shear,map_conj_mul] at hh
      exact lowerPoint_shear_generate _ hv hh
  let o := TwoConjugate.opposition (F := F)
  refine ⟨c'⁻¹*o*k,?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj c').toMonoidHom) (MulAut.conj c').injective
  rw [Subgroup.map_sup,map_conj_mul,show c'*(c'⁻¹*o*k)=o*k by group,
    ←map_conj_mul,hk,map_top_of_surjective _ (MulAut.conj c').surjective]
  exact hgen

end Theory.SpecificGroups.SymplecticFour.PointLargeGeneration
