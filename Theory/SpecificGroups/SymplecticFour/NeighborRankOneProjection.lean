module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.GroupTheory.SylowKernelCore

/-!
# A compatible rank-one projection from neighboring-mover crossing

Suppose an endpoint projects onto the upper root group at a point, while
another subgroup crosses the two-core at a different point of a plane.
Move that plane across the endpoint's point using its rank-one Levi factor.
The crossing gives a nonzero lower transvection in the same quotient.
Together with the endpoint's full upper root group this generates SL₂.

The same conjugator retains the literal parabolic crossing. Adjoining the
whole point-parabolic two-core gives the full point-local subgroup; no
containment of the ambient quotient kernel in the mover is asserted.
The replacement-graph application is in
NonbinarySymplectic.CriticalReduction.ContainedRankOneProjection.
Source: MS93 (5.5), printed p.916, the equality following the definition of F.
The subsequent individual/paired generation split is a further argument.
-/

public noncomputable section
open Subgroup Matrix Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.NeighborRankOneProjection
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private def flip : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0,1;1,0],by simp [det_fin_two,CharTwo.neg_eq]⟩
private def turn : pointLocal (F := F) := pointLevi flip

omit [Finite F] in
private theorem quotient_turn : pointQuotient (turn (F := F)) = flip :=
  pointQuotient_pointLevi _

omit [CharP F 2] [Finite F] in
private theorem shear_local (u w v : F) : (element 0 u w v).val ∈ pointLocal := by
  apply (show unipotent ≤ pointLocal (F := F) from inf_le_left)
  exact (element 0 u w v).property

omit [Finite F] in
private theorem shear_quotient (u w v : F) :
    pointQuotient (⟨(element 0 u w v).val,shear_local u w v⟩ : pointLocal) =
      SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one v := by
  apply Subtype.ext
  change pointQuotientMatrix _ = _
  simp only [pointQuotientMatrix,Matrix.submatrix]
  change (fun i j => (element 0 u w v).val.val (middleIndex i) (middleIndex j)) = _
  rw [element_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleIndex,Matrix.fromBlocks,SpecialLinearGroup.transvection_coe,Matrix.single]

omit [Finite F] in
private theorem flip_upper (v : F) :
    flip * SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one v * flip⁻¹ =
      SpecialLinearGroup.transvection (i := 1) (j := 0) one_ne_zero v := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change !![0,1;1,0] * (SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one v).val =
    (SpecialLinearGroup.transvection (i := 1) (j := 0) one_ne_zero v).val * !![0,1;1,0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two]

omit [CharP F 2] [Finite F] in
private theorem plane_core_normalized (s : Sp F) (hs : s∈planeLocal) :
    (planeParabolic.pCoreIn 2).map (MulAut.conj s).toMonoidHom =
      (planeParabolic (F := F)).pCoreIn 2 := by
  have hsP := planeLocal_le hs
  have he := mem_normalizer_iff_map_conj_eq.mp (planeParabolic.le_normalizer hsP)
  change planeParabolic.map (MulAut.conj s).toMonoidHom = planeParabolic at he
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj s).injective,he]

/-- Crossing at one point can be placed opposite the endpoint's full upper
root projection. The resulting generated subgroup has the entire rank-one
quotient, with the same point and both literal parabolic cores. -/
theorem exists_rankOne_projection {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (A E : Subgroup (Sp F))
    (hA : (A.subgroupOf pointLocal).map pointQuotient = SpecialLinearGroup.upperUnipotent F)
    (s : Sp F) (hs : s∈planeLocal)
    (hcross : ¬ E ⊓ (planeParabolic (F := F)).pCoreIn 2 ≤
      ((pointParabolic (F := F)).map (MulAut.conj s).toMonoidHom).pCoreIn 2) :
    ∃ w : Sp F, w*s∈pointLocal ∧
      ((planeParabolic (F := F)).pCoreIn 2).map (MulAut.conj w).toMonoidHom ≤ pointLocal ∧
      (¬ E.map (MulAut.conj w).toMonoidHom ⊓
        (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤
          (pointParabolic (F := F)).pCoreIn 2) ∧
      ((A ⊔ E.map (MulAut.conj w).toMonoidHom).subgroupOf pointLocal).map pointQuotient = ⊤ ∧
      (A ⊔ E.map (MulAut.conj w).toMonoidHom) ⊓ pointLocal ⊔
        (pointParabolic (F := F)).pCoreIn 2 = pointLocal := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨e,⟨heE,heP⟩,hen⟩ := SetLike.not_le_iff_exists.mp hcross
  let y : Sp F := s⁻¹*e*s
  have hyP : y∈(planeParabolic (F := F)).pCoreIn 2 := by
    rw [←plane_core_normalized s⁻¹ (planeLocal.inv_mem hs)]
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using
      mem_map_of_mem (MulAut.conj s⁻¹).toMonoidHom heP
  have hyn : y∉(pointParabolic (F := F)).pCoreIn 2 := by
    intro hy
    apply hen
    rw [←map_pCoreIn_of_injective 2 _ _ (MulAut.conj s).injective]
    refine ⟨y,hy,?_⟩
    dsimp [y,MulAut.conj_apply]
    group
  rw [pCoreIn,planeParabolic_core_map_eq_radical hF hn] at hyP
  change y∈SymplecticConjugatePair.planeRadical at hyP
  rw [SymplecticConjugatePair.planeRadical_eq_wing] at hyP
  obtain ⟨k,hk,he⟩ := hyP
  obtain ⟨⟨b,u,z,v⟩,rfl⟩ := element_surjective k
  have hb : b=0 := (element_mem_wing true _ _ _ _).mp hk
  subst b
  have hv : v≠0 := by
    intro hv
    apply hyn
    rw [pCoreIn,pointParabolic_core_map_eq_radical hF hn]
    change y∈SymplecticConjugatePair.pointRadical
    rw [SymplecticConjugatePair.pointRadical_eq_wing,←he]
    exact mem_map_of_mem unipotent.subtype ((element_mem_wing false _ _ _ _).mpr hv)
  let y₀ : pointLocal (F := F) := ⟨y,by rw [←he]; exact shear_local u z v⟩
  have hyq : pointQuotient y₀ = SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one v := by
    have he' : y₀=⟨(element 0 u z v).val,shear_local u z v⟩ := Subtype.ext he.symm
    rw [he',shear_quotient]
  let w : Sp F := (turn (F := F)).val*s⁻¹
  let D := A ⊔ E.map (MulAut.conj w).toMonoidHom
  let I := (D.subgroupOf pointLocal).map pointQuotient
  have ht : w*s∈pointLocal := by simp only [w,mul_assoc,inv_mul_cancel,mul_one]; exact turn.property
  have hplane : ((planeParabolic (F := F)).pCoreIn 2).map (MulAut.conj w).toMonoidHom ≤ pointLocal := by
    rintro x ⟨k,hk,rfl⟩
    have hk' : s⁻¹*k*s∈(planeParabolic (F := F)).pCoreIn 2 := by
      rw [←plane_core_normalized s⁻¹ (planeLocal.inv_mem hs)]
      simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using
        mem_map_of_mem (MulAut.conj s⁻¹).toMonoidHom hk
    have hkL : s⁻¹*k*s∈pointLocal := by
      rw [pCoreIn,planeParabolic_core_map_eq_radical hF hn] at hk'
      change s⁻¹*k*s∈SymplecticConjugatePair.planeRadical at hk'
      rw [SymplecticConjugatePair.planeRadical_eq_wing] at hk'
      exact (show unipotent ≤ pointLocal (F := F) from inf_le_left) (map_subtype_le _ hk')
    have hh := pointLocal.mul_mem (pointLocal.mul_mem turn.property hkL)
      (pointLocal.inv_mem turn.property)
    simpa [w,MulAut.conj_apply,mul_assoc] using hh
  have hUI : SpecialLinearGroup.upperUnipotent F ≤ I := by
    rw [←hA]
    exact map_mono (comap_mono le_sup_left)
  let x : pointLocal (F := F) := turn*y₀*turn⁻¹
  have hxD : x.val∈D := by
    apply (show E.map (MulAut.conj w).toMonoidHom ≤ D from le_sup_right)
    refine ⟨e,heE,?_⟩
    change w*e*w⁻¹=turn.val*y*turn.val⁻¹
    dsimp [w,y]
    group
  have hqx : pointQuotient x = SpecialLinearGroup.transvection (i := 1) (j := 0) one_ne_zero v := by
    dsimp only [x]
    rw [map_mul,map_mul,map_inv,hyq,quotient_turn,flip_upper]
  have hxI : pointQuotient x ∈ I := mem_map_of_mem pointQuotient hxD
  have hfull : I=⊤ := by
    by_contra hnI
    have hh := SpecialLinearGroup.overgroup_le_rankOneBorel hUI hnI hxI
    rw [hqx,SpecialLinearGroup.mem_rankOneBorel_iff] at hh
    exact hv (by simpa [SpecialLinearGroup.transvection_coe] using hh)
  have hpoint : (pointParabolic.map (MulAut.conj s).toMonoidHom).map
      (MulAut.conj w).toMonoidHom = pointParabolic := by
    rw [Subgroup.map_map]
    have he : (MulAut.conj w).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
        (MulAut.conj (w*s)).toMonoidHom := by
      ext k
      simp [MulAut.conj_apply,mul_assoc]
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp
      (pointParabolic.le_normalizer (pointLocal_le ht))
  have hcross' : ¬ E.map (MulAut.conj w).toMonoidHom ⊓
      (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤
        (pointParabolic (F := F)).pCoreIn 2 := by
    intro hle
    apply hcross
    apply (map_le_map_iff_of_injective (f := (MulAut.conj w).toMonoidHom)
      (MulAut.conj w).injective).mp
    rw [map_inf _ _ _ (MulAut.conj w).injective,
      map_pCoreIn_of_injective 2 _ _ (MulAut.conj w).injective,
      map_pCoreIn_of_injective 2 _ _ (MulAut.conj w).injective,hpoint]
    exact hle
  refine ⟨w,ht,hplane,hcross',hfull,?_⟩
  have hsupp : D.subgroupOf pointLocal ⊔ pointQuotient.ker = ⊤ := by
    rw [←comap_map_eq]
    change I.comap pointQuotient = ⊤
    rw [hfull,comap_top]
  have hh := congrArg (Subgroup.map pointLocal.subtype) hsupp
  rw [Subgroup.map_sup,subgroupOf_map_subtype,pointQuotient_ker,
    ←MonoidHom.range_eq_map,range_subtype] at hh
  rw [pCoreIn,pointParabolic_core_map_eq_radical hF hn]
  exact hh

end Theory.SpecificGroups.SymplecticFour.NeighborRankOneProjection
