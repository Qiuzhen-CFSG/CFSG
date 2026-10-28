module

public import Theory.SpecificGroups.PSL3.PointRadicalGeneration
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.GroupTheory.SylowKernelCore

/-!
# The full point-parabolic core and radical minimality

For a line in F³ over a finite field of characteristic two, the two-core of
its full setwise stabilizer is precisely the subgroup fixing the line pointwise
and acting trivially on the quotient. The scalar character on the line kills
every two-element, reducing the upper bound to the checked pointwise-local
core calculation. Normality and elementarity give the reverse inclusion.

Any nontrivial subgroup of this radical normalized by the parabolic is the
whole radical. Affine coordinates identify the Levi action with the natural
SL₂ action on additive F², which is transitive on nonzero vectors. This argument
applies to arbitrary additive subgroups, without assuming F-linearity; in fact
the minimality result does not require characteristic two. Actual SL₃
conjugators transport both calculations from the standard point to every line.
No restriction excluding F₂ is needed.

Source: Aschbacher–Smith, G.2.5(1), printed pp.335–336, and the full-normalizer
argument of G.2.3, printed pp.333–334. The source application is in
`CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Radical.Geometry.ParabolicCore`.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.PSL3.PointRadicalGeneration
open LinearThree
variable {F : Type*} [Field F] [Finite F]

private def pointScalar : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := by simp
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h).mp h.property
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]

omit [Finite F] in
private theorem standard_radical_map :
    (pointRadicalSL F).map (pointLocalSL F).subtype = radical (standardPoint (F := F)) := by
  ext u
  rw [radical_standardPoint, RootPlaneGeometry.mem_rootPlaneSL_point]
  constructor
  · rintro ⟨u,hu,rfl⟩
    have h0 := (mem_pointLocalSL_iff F u.val).mp u.property
    have h1 := (mem_pointRadicalSL_iff F u).mp hu
    refine ⟨u.val.val 0 1, u.val.val 0 2, ?_⟩
    apply Subtype.ext
    change Matrix.PSL3Even.UnipotentGeometry.matrix F _ = u.val.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.PSL3Even.UnipotentGeometry.matrix, h0.1, h0.2.1, h0.2.2,
        h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
  · rintro ⟨a,b,rfl⟩
    let u := Matrix.PSL3Even.UnipotentGeometry.specialLinear F
      ⟨a,0,b⟩
    have hu : u ∈ pointLocalSL F := by
      rw [mem_pointLocalSL_iff]
      exact ⟨rfl,rfl,rfl⟩
    refine ⟨⟨u,hu⟩, ?_, rfl⟩
    exact (mem_pointRadicalSL_iff F ⟨u,hu⟩).mpr ⟨rfl,rfl,rfl,rfl⟩

omit [Finite F] in
private theorem standard_radical_le_local :
    radical (standardPoint (F := F)) ≤ pointLocalSL F := by
  rw [← standard_radical_map]
  exact map_subtype_le _

variable [CharP F 2]
private theorem standard_core_le_local :
    (pointParabolicSL F).pCoreIn 2 ≤ pointLocalSL F := by
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := pointParabolicSL F)).exists_pow_pow_eq_one ⟨x,hx⟩
  have he : (pointScalar x) ^ (2 ^ k) = 1 := by
    have he := congrArg
      (fun y : pCore 2 (pointParabolicSL F) => pointScalar (y : pointParabolicSL F)) hk
    simpa only [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one] using he
  have hz : (pointScalar x - 1) ^ (2 ^ k) = 0 := by
    rw [sub_pow_char_pow, he, one_pow, sub_self]
  have hs : pointScalar x = 1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  exact (mem_pointLocalSL_iff F x).mpr
    ⟨hs, (mem_pointParabolicSL_iff F x).mp x.property⟩

private theorem standard_parabolic_core :
    (parabolic (standardPoint (F := F))).pCoreIn 2 = radical standardPoint := by
  apply le_antisymm
  · rw [parabolic_standardPoint]
    have hn : pointParabolicSL F ≤
        normalizer ((pointParabolicSL F).pCoreIn 2 : Set SL(3,F)) := by
      have hn := (pCore 2 (pointParabolicSL F)).le_normalizer_map (pointParabolicSL F).subtype
      rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
    have hc := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (pointParabolicSL F))
      standard_core_le_local ((pointLocalSL_le F).trans hn)
    rw [show (pointLocalSL F).pCoreIn 2 = radical standardPoint by
      rw [pCoreIn, pointLocalSL_twoCore_eq, standard_radical_map]] at hc
    exact hc
  · let : IsElementaryAbelian 2 (radical (standardPoint (F := F))) :=
      IsElementaryAbelian.of_surjective (standardRadicalEquiv (F := F)).symm.toMonoidHom
        (standardRadicalEquiv (F := F)).symm.surjective
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
      (radical_le_parabolic _) (parabolic_normalizes_radical _)

omit [Finite F] [CharP F 2] in
private theorem affine_minimal (K : Subgroup (Matrix.SL2.Affine F))
    (hK : K ≤ Matrix.SL2.translations F) (hK0 : K ≠ ⊥) [K.Normal] :
    K = Matrix.SL2.translations F := by
  let B := K.comap (SemidirectProduct.inl : Multiplicative (Fin 2 → F) →* Matrix.SL2.Affine F)
  have hB : ∀ g v, v ∈ B → Matrix.SL2.naturalAction F g v ∈ B := by
    intro g v hv
    change SemidirectProduct.inl (Matrix.SL2.naturalAction F g v) ∈ K
    rw [SemidirectProduct.inl_aut]
    simpa only [map_inv] using
      (inferInstance : K.Normal).conj_mem _ hv (SemidirectProduct.inr g)
  rcases Matrix.SL2.naturalAction_irreducible F B hB with hb | hb
  · exfalso
    apply hK0
    apply le_bot_iff.mp
    intro x hx
    have ht := hK hx
    rw [← Matrix.SL2.range_inl_eq_translations] at ht
    obtain ⟨v,rfl⟩ := ht
    have hv : v ∈ B := hx
    rw [hb, mem_bot] at hv
    simp [hv]
  · apply le_antisymm hK
    intro x hx
    rw [← Matrix.SL2.range_inl_eq_translations] at hx
    obtain ⟨v,rfl⟩ := hx
    exact (show v ∈ B from hb ▸ mem_top v)

omit [CharP F 2] in
private theorem standard_minimal (A : Subgroup SL(3,F))
    (hA : A ≤ radical (standardPoint (F := F))) (hA0 : A ≠ ⊥)
    (hn : parabolic (standardPoint (F := F)) ≤ normalizer (A : Set SL(3,F))) :
    A = radical standardPoint := by
  let L := pointLocalSL F
  let e := pointLocalAffineEquiv F
  have hAL : A ≤ L := hA.trans standard_radical_le_local
  let B := A.subgroupOf L
  have hBR : B ≤ pointRadicalSL F := by
    intro x hx
    have hr := hA hx
    rw [← standard_radical_map] at hr
    obtain ⟨y,hy,he⟩ := hr
    have hxy : y = x := Subtype.ext he
    change y ∈ pointRadicalSL F at hy
    exact hxy ▸ hy
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer hAL).mpr (by
    rw [parabolic_standardPoint] at hn
    exact (pointLocalSL_le F).trans hn)
  let K := B.map e.toMonoidHom
  let : K.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have hK : K ≤ Matrix.SL2.translations F := by
    rintro _ ⟨x,hx,rfl⟩
    exact hBR hx
  have hK0 : K ≠ ⊥ := by
    intro hk
    have hb : B = ⊥ := (map_eq_bot_iff_of_injective B e.injective).mp hk
    apply hA0
    rw [← map_subgroupOf_eq_of_le hAL]
    simpa only [Subgroup.map_bot] using congrArg (Subgroup.map L.subtype) hb
  have he := affine_minimal K hK hK0
  apply le_antisymm hA
  intro x hx
  have hxL := standard_radical_le_local hx
  let y : L := ⟨x,hxL⟩
  have hyr : y ∈ pointRadicalSL F := by
    rw [← standard_radical_map] at hx
    obtain ⟨z,hz,hzy⟩ := hx
    have hyz : z = y := Subtype.ext hzy
    change z ∈ pointRadicalSL F at hz
    exact hyz ▸ hz
  have hyK : e y ∈ K := by
    rw [he]
    exact hyr
  obtain ⟨z,hz,hzy⟩ := hyK
  have hzy' : z = y := e.injective hzy
  have hyB : y ∈ B := hzy' ▸ hz
  exact hyB

omit [Finite F] [CharP F 2] in
/-- The full point stabilizer follows the same inverse-matrix convention as the radical. -/
theorem parabolic_conjugate (P : Submodule F (Fin 3 → F)) (a : SL(3,F)) :
    (parabolic P).map (MulAut.conj a⁻¹).toMonoidHom = parabolic (conjugatePoint P a) := by
  have hc : (conjugatePoint P a : Set (Fin 3 → F)) = a⁻¹ • (P : Set (Fin 3 → F)) := rfl
  change (MulAction.stabilizer SL(3,F) (P : Set (Fin 3 → F))).map _ =
    MulAction.stabilizer SL(3,F) (conjugatePoint P a : Set (Fin 3 → F))
  rw [hc, MulAction.stabilizer_smul_eq_stabilizer_map_conj]

/-- Over every finite field of characteristic two, the full point-parabolic core is the
concrete transvection radical. This includes the field of two elements. -/
theorem parabolic_twoCore_eq (P : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 1) : (parabolic P).pCoreIn 2 = radical P := by
  obtain ⟨a,rfl⟩ := exists_standardPoint_conjugator P hP
  rw [← parabolic_conjugate, ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj a⁻¹).injective,
    standard_parabolic_core, radical_conjugate]

omit [CharP F 2] in
/-- A nontrivial subgroup of the radical invariant under the full parabolic is the
whole radical. No vector-space structure on the subgroup is assumed. -/
theorem radical_minimal (P : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 1) (A : Subgroup SL(3,F))
    (hA : A ≤ radical P) (hA0 : A ≠ ⊥)
    (hn : parabolic P ≤ normalizer (A : Set SL(3,F))) : A = radical P := by
  obtain ⟨a,ha⟩ := exists_standardPoint_conjugator P hP
  let e := MulAut.conj a⁻¹
  have hr : (radical (standardPoint (F := F))).map e.toMonoidHom = radical P := by
    rw [radical_conjugate, ha]
  have hp : (parabolic (standardPoint (F := F))).map e.toMonoidHom = parabolic P := by
    rw [parabolic_conjugate, ha]
  let B := A.comap e.toMonoidHom
  have hB : B ≤ radical standardPoint := by
    intro x hx
    have h := hA hx
    rw [← hr, mem_map_equiv] at h
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.symm_apply_apply] using h
  have hB0 : B ≠ ⊥ := by
    intro hb
    apply hA0
    have he := congrArg (Subgroup.map e.toMonoidHom) hb
    simpa only [B, map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      Subgroup.map_bot] using he
  have hBn : parabolic (standardPoint (F := F)) ≤ normalizer (B : Set SL(3,F)) := by
    rw [← comap_normalizer_eq_of_surjective A e.surjective]
    intro x hx
    apply hn
    rw [← hp]
    exact mem_map_of_mem _ hx
  have he := congrArg (Subgroup.map e.toMonoidHom) (standard_minimal B hB hB0 hBn)
  simpa only [B, map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective, hr] using he
end Matrix.PSL3.PointRadicalGeneration
