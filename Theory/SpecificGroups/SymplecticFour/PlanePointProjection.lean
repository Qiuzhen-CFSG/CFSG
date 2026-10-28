module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Thompson
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# A full rank-one projection of a large additive plane subgroup

A subgroup of the symplectic plane radical with at least q² elements has
full Sylow two-image in the point-local quotient at some other point of
that plane. The subgroup need only be additive over the prime field.

In symmetric-matrix coordinates (u,w,v), the trace annihilator has at most
q elements. If every evaluation u+t²v failed to surject, its nonzero trace
annihilator would supply q distinct nonzero elements of that annihilator,
a contradiction. An explicit plane Levi matrix realizes the chosen
evaluation in the actual pointQuotient. Adjoining the point-parabolic
two-core therefore gives the full standard Sylow, with its entire kernel.

Source: the Sylow projection condition (*) in MS93 (5.5), printed p.916,
contained large-image branch. The actual endpoint and full-cover consumer
is NonbinarySymplectic.CriticalReduction.ContainedPointProjection.
-/

public noncomputable section
open Matrix Subgroup Theory.GroupTheory
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.PlanePointProjection
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
private abbrev V (F : Type*) := F × F × F
private def dot (a v : V F) : F := a.1*v.1+a.2.1*v.2.1+a.2.2*v.2.2
private def shear (v : V F) : Sp F := (element 0 v.1 v.2.1 v.2.2).val
variable [Algebra (ZMod 2) F]
private def traceDot : LinearMap.BilinForm (ZMod 2) (V F) where
  toFun a := {
    toFun v := Algebra.trace (ZMod 2) F (dot a v)
    map_add' v w := by
      have he : dot a (v+w)=dot a v+dot a w := by dsimp [dot]; ring
      rw [he,map_add]
    map_smul' r v := by
      have he : dot a (r • v)=r • dot a v := by dsimp [dot]; simp only [Algebra.smul_def]; ring
      rw [he,map_smul]
      rfl }
  map_add' a b := by
    apply LinearMap.ext
    intro v
    have he : dot (a+b) v=dot a v+dot b v := by dsimp [dot]; ring
    change Algebra.trace (ZMod 2) F (dot (a+b) v)=_
    rw [he,map_add]
    rfl
  map_smul' r a := by
    apply LinearMap.ext
    intro v
    have he : dot (r • a) v=r • dot a v := by dsimp [dot]; simp only [Algebra.smul_def]; ring
    change Algebra.trace (ZMod 2) F (dot (r • a) v)=_
    rw [he,map_smul]
    rfl
omit [CharP F 2] [Finite F] in
private theorem traceDot_symm (a v : V F) : traceDot a v=traceDot v a := by
  change Algebra.trace (ZMod 2) F (dot a v)=Algebra.trace (ZMod 2) F (dot v a)
  congr 1
  dsimp [dot]
  ring
omit [CharP F 2] in
private theorem traceDot_nondegenerate : (traceDot (F := F)).Nondegenerate := by
  have hleft (a : V F) (ha : ∀ v, traceDot a v=0) : a=0 := by
    have h0 : a.1=0 := (traceForm_nondegenerate (ZMod 2) F).1 a.1 (by
      intro t
      simpa [traceDot,dot,Algebra.traceForm_apply] using ha (t,0,0))
    have h1 : a.2.1=0 := (traceForm_nondegenerate (ZMod 2) F).1 a.2.1 (by
      intro t
      simpa [traceDot,dot,Algebra.traceForm_apply] using ha (0,t,0))
    have h2 : a.2.2=0 := (traceForm_nondegenerate (ZMod 2) F).1 a.2.2 (by
      intro t
      simpa [traceDot,dot,Algebra.traceForm_apply] using ha (0,0,t))
    exact Prod.ext h0 (Prod.ext h1 h2)
  exact ⟨hleft,fun a ha => hleft a (fun v => (traceDot_symm a v).trans (ha v))⟩
omit [CharP F 2] in
private theorem card_orthogonal (S : Submodule (ZMod 2) (V F)) :
    Nat.card S * Nat.card (traceDot.orthogonal S) = Nat.card F^3 := by
  have hd := (traceDot (F := F)).finrank_add_finrank_orthogonal' S
  rw [traceDot_nondegenerate.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hd
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := traceDot.orthogonal S),
    ←pow_add,hd,←Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V F)]
  simp only [V,Nat.card_prod]
  ring


private def evaluation (t : F) : V F →ₗ[ZMod 2] F where
  toFun v := v.1+t^2*v.2.2
  map_add' v w := by dsimp; ring
  map_smul' r v := by
    change r • v.1+t^2*(r • v.2.2) = r • (v.1+t^2*v.2.2)
    simp only [Algebra.smul_def]
    ring

private theorem exists_surjective_evaluation
    (S : Submodule (ZMod 2) (V F)) (hc : Nat.card F^2 ≤ Nat.card S) :
    ∃ t : F, S.map (evaluation t) = ⊤ := by
  classical
  let W := (traceDot (F := F)).orthogonal S
  have hcW : Nat.card W ≤ Nat.card F := by
    have hh := card_orthogonal S
    change Nat.card S * Nat.card W = Nat.card F^3 at hh
    have hp : 0 < Nat.card F^2 := pow_pos Nat.card_pos _
    nlinarith [Nat.mul_le_mul_right (Nat.card W) hc]
  by_contra! hn
  have hex (t : F) : ∃ k : F, k≠0 ∧ (k,0,k*t^2) ∈ W := by
    let T := S.map (evaluation t)
    have hd := (Algebra.traceForm (ZMod 2) F).finrank_add_finrank_orthogonal' T
    rw [(traceForm_nondegenerate (ZMod 2) F).ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hd
    have ho : (Algebra.traceForm (ZMod 2) F).orthogonal T ≠ ⊥ := by
      intro he
      rw [he,finrank_bot,add_zero] at hd
      exact hn t (Submodule.eq_top_of_finrank_eq hd)
    obtain ⟨k,hk,hkn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ho
    refine ⟨k,hkn,?_⟩
    intro v hv
    change Algebra.trace (ZMod 2) F (dot v (k,0,k*t^2))=0
    have hh := hk (evaluation t v) (Submodule.mem_map.mpr ⟨v,hv,rfl⟩)
    change Algebra.trace (ZMod 2) F ((evaluation t v)*k)=0 at hh
    convert hh using 2
    dsimp [dot,evaluation]
    ring
  choose k hkn hk using hex
  let f : F → {w : W // w≠0} := fun t =>
    ⟨⟨(k t,0,k t*t^2),hk t⟩,fun he => hkn t (congrArg (fun w : W => w.val.1) he)⟩
  have hfi : Function.Injective f := by
    intro s t he
    have h1 : k s=k t := congrArg (fun w : {w : W // w≠0} => w.val.val.1) he
    have h2 : k s*s^2=k t*t^2 := congrArg (fun w : {w : W // w≠0} => w.val.val.2.2) he
    rw [h1] at h2
    have hp := mul_left_cancel₀ (hkn t) h2
    exact (frobeniusEquiv F 2).injective hp
  have hh := Nat.card_le_card_of_injective f hfi
  let := Fintype.ofFinite W
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_unique] at hh
  rw [←Nat.card_eq_fintype_card] at hh
  have hp : 0 < Nat.card W := Nat.card_pos
  omega

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem shear_add (v w : V F) : shear (v+w)=shear v*shear w := by
  change (element 0 (v+w).1 (v+w).2.1 (v+w).2.2).val =
    (element 0 v.1 v.2.1 v.2.2 * element 0 w.1 w.2.1 w.2.2).val
  rw [element_mul]
  simp
omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
private theorem shear_zero : shear (0 : V F)=1 := by
  simp [shear,element,RootSubgroup.element_zero]
omit [Finite F] [Algebra (ZMod 2) F] in
private theorem shear_injective : Function.Injective (shear (F := F)) := by
  intro v w he
  have hh := (element_eq_iff _ _ _ _ _ _ _ _).mp (Subtype.ext he)
  exact Prod.ext hh.2.1 (Prod.ext hh.2.2.1 hh.2.2.2)
private abbrev P : Subgroup (Sp F) := (wing true).map unipotent.subtype
omit [Algebra (ZMod 2) F] in
private theorem mem_P (x : Sp F) : x∈P ↔ ∃ v : V F, shear v=x := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
    have hb : b=0 := (element_mem_wing true _ _ _ _).mp hy
    subst b
    exact ⟨(u,w,v),rfl⟩
  · rintro ⟨v,rfl⟩
    exact mem_map_of_mem unipotent.subtype ((element_mem_wing true _ _ _ _).mpr rfl)
private def coordinates (A : Subgroup (Sp F)) : AddSubgroup (V F) where
  carrier := {v | shear v∈A}
  zero_mem' := by change shear 0∈A; rw [shear_zero]; exact A.one_mem
  add_mem' := by intro v w hv hw; change shear (v+w)∈A; rw [shear_add]; exact A.mul_mem hv hw
  neg_mem' := by
    intro v hv
    have hn : -v=v := by ext <;> simp [CharTwo.neg_eq]
    change shear (-v)∈A
    rw [hn]
    exact hv
omit [Algebra (ZMod 2) F] in
private theorem coordinates_card (A : Subgroup (Sp F)) (hA : A≤P) :
    Nat.card (coordinates A)=Nat.card A := by
  let f : coordinates A → A := fun v => ⟨shear v.val,v.property⟩
  apply Nat.card_congr (Equiv.ofBijective f ⟨?_,?_⟩)
  · intro v w he
    have he' : shear v.val=shear w.val := congrArg (fun y : A => y.val) he
    exact Subtype.ext (shear_injective he')
  · intro x
    obtain ⟨v,hv⟩ := (mem_P x.val).mp (hA x.property)
    exact ⟨⟨v,by change shear v∈A; rw [hv]; exact x.property⟩,Subtype.ext hv⟩


omit [Algebra (ZMod 2) F] in
private def selector (t : F) : Sp F :=
  rootElement 7 t * (rootElement 6 1 * rootElement 7 1 * rootElement 6 1)

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem selector_matrix (t : F) : (selector t).val =
    fromBlocks !![0,1;1,t] 0 0 !![t,1;1,0] := by
  change rootMatrix 7 t * (rootMatrix 6 1 * rootMatrix 7 1 * rootMatrix 6 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero]

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem selector_conjugate (t : F) (v : V F) :
    selector t * shear v * (selector t)⁻¹ =
      shear (v.2.2,v.2.1+t*v.2.2,v.1+t^2*v.2.2) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (selector t).val * (element 0 v.1 v.2.1 v.2.2).val.val =
    (element 0 v.2.2 (v.2.1+t*v.2.2) (v.1+t^2*v.2.2)).val.val * (selector t).val
  rw [selector_matrix,element_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks]
  all_goals ring_nf; simp [CharTwo.two_eq_zero]

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem selector_plane (t : F) : selector t ∈ planeLocal := by
  apply (Plane.mem_local_iff _).mpr
  refine ⟨?_,?_⟩
  · rw [mem_planeParabolic_iff]
    intro i j
    rw [selector_matrix]
    rfl
  · rw [selector_matrix]
    simp [Matrix.toBlocks₁₁,Matrix.fromBlocks,Matrix.det_fin_two,CharTwo.neg_eq]

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem selector_not_point (t : F) : selector t ∉ pointParabolic := by
  intro h
  have hh := ((mem_pointParabolic_iff _).mp h).1
  rw [selector_matrix] at hh
  exact one_ne_zero hh

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem shear_point (v : V F) : shear v ∈ pointLocal := by
  rw [mem_pointLocal_iff_fixed]
  funext i
  change ((element 0 v.1 v.2.1 v.2.2).val.val *ᵥ e 0) i = (e (F := F) 0) i
  rw [element_matrix]
  rcases i with i | i <;> fin_cases i <;>
    simp [e,Matrix.mulVec_single,Matrix.fromBlocks]

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem shear_quotient (v : V F) :
    pointQuotient (⟨shear v,shear_point v⟩ : pointLocal) =
      SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one v.2.2 := by
  apply Subtype.ext
  change pointQuotientMatrix _ = _
  simp only [pointQuotientMatrix,Matrix.submatrix]
  change (fun i j => (element 0 v.1 v.2.1 v.2.2).val.val (middleIndex i) (middleIndex j)) = _
  rw [element_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleIndex,Matrix.fromBlocks,SpecialLinearGroup.transvection_coe,Matrix.single]

/-- A plane subgroup of order at least q² projects onto a Sylow two-subgroup
at some different point of the same plane. The image uses the actual action
on the perpendicular space modulo that point, without a full-root premise. -/
theorem exists_sylow_projection (A : Subgroup (Sp F))
    (hAP : A ≤ (wing true).map unipotent.subtype) (hc : Nat.card F^2 ≤ Nat.card A) :
    ∃ g : Sp F, g ∈ planeLocal ∧ g ∉ pointParabolic ∧
      A.map (MulAut.conj g).toMonoidHom ≤ (wing true).map unipotent.subtype ∧
      ((A.map (MulAut.conj g).toMonoidHom).subgroupOf pointLocal).map pointQuotient =
        SpecialLinearGroup.upperUnipotent F := by
  let S := AddSubgroup.toZModSubmodule 2 (coordinates A)
  have hcS : Nat.card F^2 ≤ Nat.card S := by
    change Nat.card F^2 ≤ Nat.card (coordinates A)
    rwa [coordinates_card A hAP]
  obtain ⟨t,ht⟩ := exists_surjective_evaluation S hcS
  have hle : A.map (MulAut.conj (selector t)).toMonoidHom ≤ P := by
    rintro y ⟨w,hw,rfl⟩
    obtain ⟨v,rfl⟩ := (mem_P w).mp (hAP hw)
    change selector t * shear v * (selector t)⁻¹ ∈ P
    rw [selector_conjugate]
    exact (mem_P _).mpr ⟨_,rfl⟩
  refine ⟨selector t,selector_plane t,selector_not_point t,hle,le_antisymm ?_ ?_⟩
  · rintro y ⟨w,hw,rfl⟩
    obtain ⟨v,hv⟩ := (mem_P w.val).mp (hle hw)
    have hwv : w = ⟨shear v,shear_point v⟩ := Subtype.ext hv.symm
    rw [hwv,shear_quotient]
    exact (SpecialLinearGroup.mem_upperUnipotent F _).mpr ⟨_,rfl⟩
  · intro y hy
    obtain ⟨r,rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent F y).mp hy
    obtain ⟨v,hv,he⟩ := Submodule.mem_map.mp (ht ▸ (Submodule.mem_top : r∈(⊤ : Submodule (ZMod 2) F)))
    let w := (v.2.2,v.2.1+t*v.2.2,v.1+t^2*v.2.2)
    refine ⟨⟨shear w,shear_point w⟩,?_,?_⟩
    · change shear w ∈ A.map (MulAut.conj (selector t)).toMonoidHom
      exact ⟨shear v,hv,selector_conjugate t v⟩
    · rw [shear_quotient]
      exact congrArg (SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one) he




/-- The selected point satisfies the full source Sylow condition: adjoining
its actual parabolic two-core to the endpoint gives the standard Sylow. -/
theorem exists_sylow_core_join {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n)
    (A : Subgroup (Sp F)) (hAP : A ≤ (wing true).map unipotent.subtype)
    (hc : Nat.card F^2 ≤ Nat.card A) :
    ∃ g : Sp F, g ∈ planeLocal ∧ g ∉ pointParabolic ∧
      A.map (MulAut.conj g).toMonoidHom ≤ (wing true).map unipotent.subtype ∧
      ((A.map (MulAut.conj g).toMonoidHom).subgroupOf pointLocal).map pointQuotient =
        SpecialLinearGroup.upperUnipotent F ∧
      A.map (MulAut.conj g).toMonoidHom ⊔ (pointParabolic (F := F)).pCoreIn 2 =
        unipotent := by
  obtain ⟨g,hg,hng,hAP',him⟩ := exists_sylow_projection A hAP hc
  let A' := A.map (MulAut.conj g).toMonoidHom
  have hAU : A' ≤ unipotent := hAP'.trans (map_subtype_le _)
  let U : Sylow 2 (pointLocal (F := F)) := (unipotentSylow hF (by omega)).subtype (show unipotent ≤ pointLocal from inf_le_left)
  have hk : IsPGroup 2 (pointQuotient (F := F)).ker := by
    rw [pointQuotient_ker]
    exact IsElementaryAbelian.isPGroup 2 pointRadical
  let T : Sylow 2 (pointLocal (F := F)) := (SpecialLinearGroup.upperUnipotentSylow F 2).comapOfKerIsPGroup
    pointQuotient hk (by rw [MonoidHom.range_eq_top.mpr pointQuotient_surjective]; exact le_top)
  have he : A'.subgroupOf pointLocal ⊔ pointQuotient.ker = (T : Subgroup (pointLocal (F := F))) := by
    rw [←comap_map_eq]
    change (((A.map (MulAut.conj g).toMonoidHom).subgroupOf pointLocal).map pointQuotient).comap
      pointQuotient = _
    rw [him]
    rfl
  have hTU : (T : Subgroup (pointLocal (F := F))) ≤ (U : Subgroup (pointLocal (F := F))) := by
    rw [←he]
    exact sup_le (comap_mono hAU) (hk.le_sylow_of_normal U)
  have hUT := T.is_maximal' U.isPGroup' hTU
  have he' := congrArg (Subgroup.map pointLocal.subtype) (he.trans hUT.symm)
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (hAU.trans inf_le_left),pointQuotient_ker] at he'
  change A' ⊔ pointRadical.map pointLocal.subtype =
    (unipotent.subgroupOf pointLocal).map pointLocal.subtype at he'
  rw [map_subgroupOf_eq_of_le (show unipotent ≤ pointLocal from inf_le_left)] at he'
  refine ⟨g,hg,hng,hAP',him,?_⟩
  change A' ⊔ _ = unipotent
  rw [pCoreIn,pointParabolic_core_map_eq_radical hF hn]
  exact he'

end Theory.SpecificGroups.SymplecticFour.PlanePointProjection
