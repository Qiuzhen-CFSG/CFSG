module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction.Model.Transport
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# The doubled contragredient parabolic calculation

For the literal dual of the binary natural SL₃-module, the point parabolic
has no fixed vectors. The line parabolic fixes only the last-coordinate
covectors. On two copies, projection onto these covectors sends each translate
of a seed vector to a scalar multiple of that same vector. Thus a fixed seed
whose SL₃-orbit spans the whole module must contain both covector lines.

The adjacent point-parabolic span is the doubled covector plane annihilating
e₀: the involution swapping e₁ and e₂ generates its other coordinate lines.
Evaluation on e₁,e₂ intertwines the full parabolic with the inverse transpose
of its lower-right block. This quotient is surjective, and its unipotent kernel
is the intrinsic two-core, by the SL₂(2)–S₃ identification. The dot-product
intertwining identity below justifies using these coordinates on Module.Dual.

This proves the dual input to Model.Transport's standard calculation contract.
Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(5), printed pp.911–912.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
open Matrix Representation
open Matrix.PSL3Two
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction
namespace DualCalculation

private abbrev F := ZMod 2
private abbrev Vec := Fin 3 → F
private abbrev Cov := Module.Dual F Vec
private abbrev Double := Cov × Cov
private noncomputable abbrev sigma := BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual

private theorem point_entries (a : pointParabolicSL) :
    a.val.val 0 0 = 1 ∧ a.val.val 1 0 = 0 ∧ a.val.val 2 0 = 0 := by
  obtain ⟨h1,h2⟩ := (mem_pointParabolicSL_iff a.val).mp a.property
  refine ⟨?_,h1,h2⟩
  have hd := a.val.property
  rw [Matrix.det_fin_three, h1, h2] at hd
  have hz : a.val.val 0 0 ≠ 0 := by
    intro h
    simp [h] at hd
  exact (by decide : ∀ x : F, x ≠ 0 → x = 1) _ hz

private def block (a : pointParabolicSL) : SL2 :=
  ⟨fun i j => a.val.val i.succ j.succ, by
    have h := a.val.property
    obtain ⟨h0,h1,h2⟩ := point_entries a
    rw [Matrix.det_fin_two]
    change a.val.val 1 1 * a.val.val 2 2 - a.val.val 1 2 * a.val.val 2 1 = 1
    simpa only [Matrix.det_fin_three, h0,h1,h2,
      zero_mul, mul_zero, one_mul, add_zero, sub_zero] using h⟩

private def blockHom : pointParabolicSL →* SL2 where
  toFun := block
  map_one' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' a b := by
    apply Subtype.ext
    ext i j
    change ∑ k : Fin 3, a.val.val i.succ k * b.val.val k j.succ =
      ∑ k : Fin 2, a.val.val i.succ k.succ * b.val.val k.succ j.succ
    obtain ⟨_,h1,h2⟩ := point_entries a
    fin_cases i <;> simp [Fin.sum_univ_three, Fin.sum_univ_two, h1,h2]

private def blockLift (a : SL2) : pointParabolicSL :=
  ⟨⟨!![1,0,0; 0,a.val 0 0,a.val 0 1; 0,a.val 1 0,a.val 1 1], by
    have h := a.property
    rw [Matrix.det_fin_two] at h
    simpa [Matrix.det_fin_three] using h⟩,
    (mem_pointParabolicSL_iff _).mpr ⟨rfl,rfl⟩⟩

private theorem block_surjective : Function.Surjective blockHom := by
  intro a
  refine ⟨blockLift a, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem transpose_mul (a b : SL2) : (a*b).transpose = b.transpose*a.transpose :=
  Subtype.ext (Matrix.transpose_mul _ _)
private theorem transpose_inv (a : SL2) : a⁻¹.transpose = a.transpose⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← transpose_mul, mul_inv_cancel]
  exact Subtype.ext Matrix.transpose_one
private def graph : MulAut SL2 where
  toFun a := a⁻¹.transpose
  invFun a := a⁻¹.transpose
  left_inv a := by
    change (a⁻¹.transpose)⁻¹.transpose = a
    rw [transpose_inv]
    change (a⁻¹)⁻¹ = a
    exact inv_inv a
  right_inv a := by
    change (a⁻¹.transpose)⁻¹.transpose = a
    rw [transpose_inv]
    change (a⁻¹)⁻¹ = a
    exact inv_inv a
  map_mul' a b := by rw [_root_.mul_inv_rev, transpose_mul]

private def quotient : pointParabolicSL →* SL2 := graph.toMonoidHom.comp blockHom

private theorem quotient_surjective : Function.Surjective quotient :=
  graph.surjective.comp block_surjective

private theorem block_ker_two : IsPGroup 2 blockHom.ker := by
  intro a
  refine ⟨1, ?_⟩
  have h := a.property
  change blockHom a.val = 1 at h
  have h11 := congrArg (fun g : SL2 => g.val 0 0) h
  have h12 := congrArg (fun g : SL2 => g.val 0 1) h
  have h21 := congrArg (fun g : SL2 => g.val 1 0) h
  have h22 := congrArg (fun g : SL2 => g.val 1 1) h
  change a.val.val.val 1 1 = 1 at h11
  change a.val.val.val 1 2 = 0 at h12
  change a.val.val.val 2 1 = 0 at h21
  change a.val.val.val 2 2 = 1 at h22
  obtain ⟨h00,h10,h20⟩ := point_entries a.val
  simp only [pow_one, pow_two]
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change a.val.val.val * a.val.val.val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h00,h10,h20,h11,h12,h21,h22,
      CharTwo.add_self_eq_zero]

private theorem quotient_ker : quotient.ker = pCore 2 pointParabolicSL := by
  have hk : quotient.ker = blockHom.ker := by
    ext a
    change graph (blockHom a) = 1 ↔ blockHom a = 1
    exact graph.map_eq_one_iff
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  have he : (e.toMonoidHom.comp blockHom).ker = blockHom.ker := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change e (blockHom a) = 1 ↔ blockHom a = 1
    exact e.map_eq_one_iff
  rw [hk, ← he]
  exact ker_eq_twoCore_of_surjective_perm_three _ (e.surjective.comp block_surjective)
    (he.symm ▸ block_ker_two)

private def dot : Vec ≃ₗ[F] Cov := dotProductEquiv F (Fin 3)
private abbrev coeff : Cov ≃ₗ[F] Vec := dot.symm

private theorem dual_dot (g : SL) (v : Vec) :
    BinaryLinearThree.W.dual g (dot v) = dot ((g⁻¹.val)ᵀ *ᵥ v) := by
  apply LinearMap.ext
  intro w
  change v ⬝ᵥ (g⁻¹.val *ᵥ w) = ((g⁻¹.val)ᵀ *ᵥ v) ⬝ᵥ w
  symm
  rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.transpose_transpose]

private theorem coeff_action (g : SL) (f : Cov) :
    coeff (BinaryLinearThree.W.dual g f) = (g⁻¹.val)ᵀ *ᵥ coeff f := by
  apply dot.injective
  rw [LinearEquiv.apply_symm_apply, ← dual_dot, LinearEquiv.apply_symm_apply]

private def coordinates : Double ≃ₗ[F] (Vec × Vec) := coeff.prodCongr coeff

private theorem coordinates_action (g : SL) (v : Double) :
    coordinates (sigma g v) =
      ((g⁻¹.val)ᵀ *ᵥ (coordinates v).1, (g⁻¹.val)ᵀ *ᵥ (coordinates v).2) := by
  exact Prod.ext (coeff_action g v.1) (coeff_action g v.2)

private def e01 : SL := ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩
private def e12 : SL := ⟨!![1,0,0; 0,1,1; 0,0,1], by decide⟩
private def e21 : SL := ⟨!![1,0,0; 0,1,0; 0,1,1], by decide⟩
private theorem e01_inv : e01⁻¹ = e01 := inv_eq_of_mul_eq_one_right (by decide)
private theorem e12_inv : e12⁻¹ = e12 := inv_eq_of_mul_eq_one_right (by decide)
private theorem e21_inv : e21⁻¹ = e21 := inv_eq_of_mul_eq_one_right (by decide)

private theorem fixed_e01 (f : Cov) (h : BinaryLinearThree.W.dual e01 f = f) :
    coeff f 0 = 0 := by
  have hh := congrArg (fun f => coeff f 1) h
  rw [coeff_action, e01_inv] at hh
  simpa [e01, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hh

private theorem fixed_e12 (f : Cov) (h : BinaryLinearThree.W.dual e12 f = f) :
    coeff f 1 = 0 := by
  have hh := congrArg (fun f => coeff f 2) h
  rw [coeff_action, e12_inv] at hh
  simpa [e12, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hh

private theorem fixed_e21 (f : Cov) (h : BinaryLinearThree.W.dual e21 f = f) :
    coeff f 2 = 0 := by
  have hh := congrArg (fun f => coeff f 1) h
  rw [coeff_action, e21_inv] at hh
  simpa [e21, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hh

private def seedCoords : Submodule F (Vec × Vec) where
  carrier := {v | v.1 0 = 0 ∧ v.1 1 = 0 ∧ v.2 0 = 0 ∧ v.2 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro v w ⟨h0,h1,h2,h3⟩ ⟨k0,k1,k2,k3⟩
    exact ⟨by simp [h0,k0], by simp [h1,k1], by simp [h2,k2], by simp [h3,k3]⟩
  smul_mem' := by
    rintro a v ⟨h0,h1,h2,h3⟩
    exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3]⟩

private def seed : Submodule F Double := seedCoords.comap coordinates.toLinearMap

private def planeCoords : Submodule F (Vec × Vec) where
  carrier := {v | v.1 0 = 0 ∧ v.2 0 = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro v w ⟨h0,h1⟩ ⟨k0,k1⟩
    exact ⟨by simp [h0,k0], by simp [h1,k1]⟩
  smul_mem' := by
    rintro a v ⟨h0,h1⟩
    exact ⟨by simp [h0], by simp [h1]⟩

private def plane : Submodule F Double := planeCoords.comap coordinates.toLinearMap

private theorem point_fixed_zero (v : Double)
    (h : v ∈ BinaryOffender.fixedSpace sigma pointParabolicSL) : v = 0 := by
  have h01 := h ⟨e01, (mem_pointParabolicSL_iff _).mpr (by decide)⟩
  have h12 := h ⟨e12, (mem_pointParabolicSL_iff _).mpr (by decide)⟩
  have h21 := h ⟨e21, (mem_pointParabolicSL_iff _).mpr (by decide)⟩
  have h00 := fixed_e01 v.1 (congrArg Prod.fst h01)
  have h01' := fixed_e12 v.1 (congrArg Prod.fst h12)
  have h02 := fixed_e21 v.1 (congrArg Prod.fst h21)
  have h10 := fixed_e01 v.2 (congrArg Prod.snd h01)
  have h11 := fixed_e12 v.2 (congrArg Prod.snd h12)
  have h12' := fixed_e21 v.2 (congrArg Prod.snd h21)
  apply coordinates.injective
  apply Prod.ext
  · ext i
    fin_cases i <;> simp_all [coordinates]
  · ext i
    fin_cases i <;> simp_all [coordinates]

private theorem line_fixed_le_seed : BinaryOffender.fixedSpace sigma lineParabolicSL ≤ seed := by
  intro v h
  have h01 := h ⟨e01, (mem_lineParabolicSL_iff _).mpr (by decide)⟩
  have h12 := h ⟨e12, (mem_lineParabolicSL_iff _).mpr (by decide)⟩
  exact ⟨fixed_e01 v.1 (congrArg Prod.fst h01), fixed_e12 v.1 (congrArg Prod.fst h12),
    fixed_e01 v.2 (congrArg Prod.snd h01), fixed_e12 v.2 (congrArg Prod.snd h12)⟩

private def projectCoords : (Vec × Vec) →ₗ[F] (Vec × Vec) where
  toFun v := (![0,0,v.1 2], ![0,0,v.2 2])
  map_add' v w := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp
  map_smul' a v := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp

private def project : Double →ₗ[F] Double :=
  coordinates.symm.toLinearMap ∘ₗ projectCoords ∘ₗ coordinates.toLinearMap

private theorem coordinates_project (v : Double) :
    coordinates (project v) = (![0,0,(coordinates v).1 2], ![0,0,(coordinates v).2 2]) :=
  coordinates.apply_symm_apply _

private theorem project_seed (v : Double) (hv : v ∈ seed) : project v = v := by
  obtain ⟨h0,h1,h2,h3⟩ := hv
  apply coordinates.injective
  rw [coordinates_project]
  apply Prod.ext <;> ext i <;> fin_cases i <;> simp_all

private theorem project_translate (g : SL) (v : Double) (hv : v ∈ seed) :
    project (sigma g v) = (g⁻¹.val 2 2) • v := by
  obtain ⟨h0,h1,h2,h3⟩ := hv
  apply coordinates.injective
  rw [coordinates_project, coordinates_action, map_smul]
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp_all [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

-- The source generation hypothesis determines the entire two-dimensional seed.
private theorem generating_seed_eq (E : Submodule F Double) (hE : E ≤ seed)
    (hgen : Seed.orbitSpace sigma ⊤ E = ⊤) : E = seed := by
  apply le_antisymm hE
  have hproj : Seed.orbitSpace sigma ⊤ E ≤ E.comap project := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, hv, rfl⟩
    change project (sigma g v) ∈ E
    rw [project_translate g v (hE hv)]
    exact E.smul_mem _ hv
  rw [hgen] at hproj
  intro v hv
  have h := hproj (Submodule.mem_top : v ∈ (⊤ : Submodule F Double))
  change project v ∈ E at h
  rwa [project_seed v hv] at h

private def swap12 : SL := ⟨!![1,0,0; 0,0,1; 0,1,0], by decide⟩
private theorem swap12_inv : swap12⁻¹ = swap12 := inv_eq_of_mul_eq_one_right (by decide)
private theorem swap12_mem : swap12 ∈ pointParabolicSL :=
  (mem_pointParabolicSL_iff _).mpr (by decide)

private def insert (a b : F) : Double := coordinates.symm (![0,0,a], ![0,0,b])
private theorem coordinates_insert (a b : F) :
    coordinates (insert a b) = (![0,0,a], ![0,0,b]) := coordinates.apply_symm_apply _
private theorem insert_mem (a b : F) : insert a b ∈ seed := by
  change (coordinates (insert a b)).1 0 = 0 ∧ _
  rw [coordinates_insert]
  exact ⟨rfl,rfl,rfl,rfl⟩

-- Both inclusions concern the literal orbit span under the adjacent parabolic.
private theorem orbit_eq_plane : Seed.orbitSpace sigma pointParabolicSL seed = plane := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    change (coordinates v).1 0 = 0 ∧ (coordinates v).1 1 = 0 ∧
      (coordinates v).2 0 = 0 ∧ (coordinates v).2 1 = 0 at hv
    obtain ⟨h0,h1,h2,h3⟩ := hv
    obtain ⟨_,k1,k2⟩ := point_entries (⟨g⁻¹, pointParabolicSL.inv_mem hg⟩)
    change (coordinates (sigma g v)).1 0 = 0 ∧ (coordinates (sigma g v)).2 0 = 0
    rw [coordinates_action]
    change g⁻¹.val 1 0 = 0 at k1
    change g⁻¹.val 2 0 = 0 at k2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
      h0,h2,k1,k2,zero_mul,mul_zero,add_zero, and_self]
  · intro v hv
    obtain ⟨h0,h1⟩ := hv
    have hdec : v = insert ((coordinates v).1 2) ((coordinates v).2 2) +
        sigma swap12 (insert ((coordinates v).1 1) ((coordinates v).2 1)) := by
      apply coordinates.injective
      rw [map_add, coordinates_insert, coordinates_action, coordinates_insert, swap12_inv]
      apply Prod.ext
      all_goals
        apply funext
        intro i
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, Matrix.transpose_apply]
        fin_cases i <;> simp_all [swap12]
    rw [hdec]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨1, pointParabolicSL.one_mem,
        insert ((coordinates v).1 2) ((coordinates v).2 2), insert_mem _ _, by simp⟩
    · exact Submodule.subset_span ⟨swap12, swap12_mem, _, insert_mem _ _, rfl⟩

private def planeEquiv : plane ≃ₗ[F] (Fin 2 → Fin 2 → F) where
  toFun v := ![![(coordinates v.val).1 1, (coordinates v.val).1 2],
    ![(coordinates v.val).2 1, (coordinates v.val).2 2]]
  invFun m := ⟨coordinates.symm (![0,m 0 0,m 0 1], ![0,m 1 0,m 1 1]), by
    change (coordinates (coordinates.symm _)).1 0 = 0 ∧
      (coordinates (coordinates.symm _)).2 0 = 0
    rw [coordinates.apply_symm_apply]
    exact ⟨rfl,rfl⟩⟩
  left_inv v := by
    apply Subtype.ext
    apply coordinates.injective
    rw [coordinates.apply_symm_apply]
    obtain ⟨h0,h1⟩ := v.property
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp_all
  right_inv m := by
    simp only [coordinates.apply_symm_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_add' v w := by
    change ![![(coordinates (v.val+w.val)).1 1, (coordinates (v.val+w.val)).1 2],
      ![(coordinates (v.val+w.val)).2 1, (coordinates (v.val+w.val)).2 2]] = _
    rw [map_add]
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_smul' a v := by
    change ![![(coordinates (a • v.val)).1 1, (coordinates (a • v.val)).1 2],
      ![(coordinates (a • v.val)).2 1, (coordinates (a • v.val)).2 2]] = _
    rw [map_smul]
    funext i j
    fin_cases i <;> fin_cases j <;> rfl

private theorem quotient_entry (a : pointParabolicSL) (i j : Fin 2) :
    (quotient a).val i j = a.val⁻¹.val j.succ i.succ := by
  change ((blockHom a)⁻¹).val j i = _
  rw [← blockHom.map_inv]
  rfl

-- This equation holds for every element, including all involutions.
private theorem planeEquiv_action (a : pointParabolicSL) (v w : plane)
    (hw : w.val = sigma a.val v.val) (j : Fin 2) :
    planeEquiv w j = (quotient a).val *ᵥ planeEquiv v j := by
  have hcoord := congrArg coordinates hw
  rw [coordinates_action] at hcoord
  obtain ⟨h0,h1⟩ := v.property
  apply funext
  intro i
  change (![![(coordinates w.val).1 1, (coordinates w.val).1 2],
    ![(coordinates w.val).2 1, (coordinates w.val).2 2]] j) i = _
  rw [hcoord]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, quotient_entry]
  fin_cases j <;> fin_cases i <;>
    simp_all [planeEquiv, Fin.sum_univ_three]

private theorem seed_orbit_coordinates : OrbitCoordinates sigma pointParabolicSL seed quotient := by
  let e := (LinearEquiv.ofEq _ _ orbit_eq_plane).trans planeEquiv
  refine ⟨e, fun a v w hw j => ?_⟩
  exact planeEquiv_action a ((LinearEquiv.ofEq _ _ orbit_eq_plane) v)
    ((LinearEquiv.ofEq _ _ orbit_eq_plane) w) hw j

private theorem no_point_seed (E : Submodule F Double)
    (hf : E ≤ BinaryOffender.fixedSpace sigma pointParabolicSL)
    (hg : Seed.orbitSpace sigma ⊤ E = ⊤) : False := by
  have hzero : Seed.orbitSpace sigma ⊤ E ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, hv, rfl⟩
    rw [point_fixed_zero v (hf hv), map_zero]
    exact Submodule.zero_mem _
  rw [hg] at hzero
  have h : insert 1 0 = 0 := hzero Submodule.mem_top
  have he := congrArg (fun v => (coordinates v).1 2) h
  simp [coordinates_insert] at he

end DualCalculation

/-- The literal doubled dual has full natural rank-one coordinates on the
adjacent parabolic orbit of every fixed generating seed. -/
theorem dual_standard_orbit_calculation :
    StandardOrbitCalculation (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual) := by
  intro i E hf hg
  cases i with
  | false => exact (DualCalculation.no_point_seed E hf hg).elim
  | true =>
    have he := DualCalculation.generating_seed_eq E
      (hf.trans DualCalculation.line_fixed_le_seed) hg
    subst E
    exact ⟨DualCalculation.quotient, DualCalculation.quotient_surjective,
      DualCalculation.quotient_ker, DualCalculation.seed_orbit_coordinates⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction
