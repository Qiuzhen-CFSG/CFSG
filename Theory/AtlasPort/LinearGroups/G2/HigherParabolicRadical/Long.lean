module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The factorization and coordinate calculations extend the licensed ATLAS
split-octonion model, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS-CITATION.cff. They adapt the existing CFSG extensions
LieLongParabolic/Quotient.lean and EvenLocal/LongCore.lean.
Changes: extend the quotient-plane action to the full long parabolic, normalize
its determinant, and identify its full solvable radical and PSL₂ quotient.
-/

public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The full long G₂ parabolic modulo its solvable radical

The point parabolic preserves the space spanned by the first three coordinate
vectors and its first-vector line. The induced two-dimensional action has
determinant equal to the scalar on that line. Over a finite field of
characteristic two, inverse Frobenius supplies a multiplicative square root;
scaling the action by the inverse square root of its determinant therefore
produces a homomorphism to SL₂. The existing local block section proves that
this homomorphism is surjective.

Its kernel is solvable: the line-scalar character has abelian image, and its
kernel inside this action kernel embeds into the five-root two-group. For
q > 2, SL₂ is nonabelian simple and has trivial solvable radical, so the action
kernel is precisely the full parabolic's solvable radical. The final
isomorphism uses the actual parabolic quotient and the canonical SL₂-to-PSL₂
map, whose central kernel is trivial in characteristic two.

Source: Aschbacher--Smith, E.1.14(1), printed p.214 (citing Aschbacher 1982,
Lemma 4.7), and the G₂ rank-one local structure in F.1.12(I)(3), printed
pp.262--264 of `refs/quasithin.pdf`. This is the full-parabolic model input
needed by the radical two-extension argument; the five-root local quotient
alone does not account for the scalar torus.
-/

public section

open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit Atlas.G2.PairStabilizer
open Atlas.G2.LieParabolicSetup
open scoped MatrixGroups Pointwise
namespace Atlas.G2.HigherParabolicRadical.Long
variable {F : Type*} [Field F] [CharP F 2]

private theorem long_factor (g : parabolic₂ (F := F)) :
    ∃ (l : Fˣ) (t : Fin 6 → F) (M : SL(2,F)), t 4 = 0 ∧
      g.val = torus l 1 * (unipotentProduct t * blockHom M) := by
  let gp : pointStabilizer (K := F) :=
    ⟨g.val, by rw [← parabolic_eq_pointStabilizer]; exact g.property⟩
  let h : fixingFirstVector (K := F) := normalizePoint gp
  have hl : h.val ∈ local₂ := by rw [local₂_eq_fixingFirstVector]; exact h.property
  rw [← SetLike.mem_coe, local₂_eq_radical₂_mul_fixingPair] at hl
  obtain ⟨u, ⟨t, ht, rfl⟩, m, hm, he⟩ := hl
  refine ⟨lineScalar gp, t, imageSL ⟨m, hm⟩, ht, ?_⟩
  have hb := congrArg Subtype.val (block_imageSL ⟨m, hm⟩)
  change blockHom (imageSL ⟨m, hm⟩) = m at hb
  change unipotentProduct t * m = h.val at he
  rw [hb, he]
  change g.val = torus (lineScalar gp) 1 * ((torus (lineScalar gp) 1)⁻¹ * g.val)
  exact (mul_inv_cancel_left _ _).symm

omit [CharP F 2] in
private theorem radical_action (t : Fin 6 → F) (ht : t 4 = 0) (a b c : F) :
    (unipotentProduct t).val ![a,b,c,0,0,0,0,0] =
    ![a - t 3 * c - t 5 * b,b,c,0,0,0,0,0] := by
  funext i
  fin_cases i <;> simp [unipotentProduct,rootA,rootB,rootC,rootD,rootE,rootF,
    rootAEquiv,rootBEquiv,rootCEquiv,rootDEquiv,rootEEquiv,rootFEquiv,
    rootALinear,rootBLinear,rootCLinear,rootDLinear,rootELinear,rootFLinear,
    rootAApply,rootBApply,rootCApply,rootDApply,rootEApply,rootFApply,ht]
  ring

private theorem factor_action (t : Fin 6 → F) (ht : t 4 = 0) (M : SL(2,F)) (a b c : F) :
    (unipotentProduct t * blockHom M).val ![a,b,c,0,0,0,0,0] =
    ![a - t 3 * (M 1 0*b + M 1 1*c) - t 5 * (M 0 0*b + M 0 1*c),
      M 0 0*b + M 0 1*c, M 1 0*b + M 1 1*c,0,0,0,0,0] := by
  change (unipotentProduct t).val (blockLinear M.val ![a,b,c,0,0,0,0,0]) = _
  have hb : blockLinear M.val ![a,b,c,0,0,0,0,0] =
      ![a,M 0 0*b + M 0 1*c,M 1 0*b + M 1 1*c,0,0,0,0,0] := by
    simp [blockLinear, sub_eq_add_neg, CharTwo.neg_eq]
  rw [hb, radical_action t ht]

private theorem full_factor_action (l : Fˣ) (t : Fin 6 → F) (ht : t 4 = 0)
    (M : SL(2,F)) (a b c : F) :
    (torus l 1 * (unipotentProduct t * blockHom M)).val ![a,b,c,0,0,0,0,0] =
    ![(l : F) * (a - t 3 * (M 1 0*b + M 1 1*c) - t 5 * (M 0 0*b + M 0 1*c)),
      M 0 0*b + M 0 1*c, (l : F) * (M 1 0*b + M 1 1*c),0,0,0,0,0] := by
  change (torus l 1).val ((unipotentProduct t * blockHom M).val _) = _
  rw [factor_action t ht]
  funext i
  fin_cases i <;> simp [torus,torusEquiv,torusLinear,torusWeights]

omit [CharP F 2] in
private theorem first_two_basis (i : Fin 2) :
    (E (if i = 0 then 1 else 2) : Carrier F) =
      if i = 0 then ![0,1,0,0,0,0,0,0] else ![0,0,1,0,0,0,0,0] := by
  fin_cases i <;> funext j <;> fin_cases j <;> simp [E,basisVector]

private theorem matrix_factor (l : Fˣ) (t : Fin 6 → F) (ht : t 4 = 0)
    (M : SL(2,F)) :
    longMatrix (torus l 1 * (unipotentProduct t * blockHom M)) =
      !![M 0 0,M 0 1; (l : F)*M 1 0,(l : F)*M 1 1] := by
  unfold longMatrix
  rw [show (E 1 : Carrier F) = ![0,1,0,0,0,0,0,0] from first_two_basis 0,
      show (E 2 : Carrier F) = ![0,0,1,0,0,0,0,0] from first_two_basis 1,
      full_factor_action l t ht, full_factor_action l t ht]
  simp

/-- The scalar character of the full long parabolic on its stabilized line. -/
def scalarHom : parabolic₂ (F := F) →* Fˣ :=
  lineScalarHom.comp (MulEquiv.subgroupCongr parabolic_eq_pointStabilizer).toMonoidHom

private theorem scalar_factor (l : Fˣ) (t : Fin 6 → F) (ht : t 4 = 0)
    (M : SL(2,F)) (g : parabolic₂ (F := F))
    (hg : g.val = torus l 1 * (unipotentProduct t * blockHom M)) :
    scalarHom g = l := by
  apply Units.ext
  change g.val.val (basisVector 0) 0 = l.val
  rw [hg]
  have h0 : (basisVector 0 : Carrier F) = ![1,0,0,0,0,0,0,0] := by
    funext i; fin_cases i <;> simp [basisVector]
  rw [h0,full_factor_action l t ht]
  simp

/-- The full parabolic preserves the three-coordinate space and its first line;
these are the entries of its induced action on their quotient. -/
theorem matrix_mul (g h : parabolic₂ (F := F)) :
    longMatrix (g.val * h.val) = longMatrix g.val * longMatrix h.val := by
  obtain ⟨l,t,M,ht,hg⟩ := long_factor g
  obtain ⟨m,u,N,hu,hh⟩ := long_factor h
  rw [hg,hh,matrix_factor l t ht,matrix_factor m u hu]
  have act (x : Carrier F) :
      ((torus l 1 * (unipotentProduct t * blockHom M)) *
        (torus m 1 * (unipotentProduct u * blockHom N))).val x =
      (torus l 1 * (unipotentProduct t * blockHom M)).val
        ((torus m 1 * (unipotentProduct u * blockHom N)).val x) := rfl
  unfold longMatrix
  rw [show (E 1 : Carrier F) = ![0,1,0,0,0,0,0,0] from first_two_basis 0,
      show (E 2 : Carrier F) = ![0,0,1,0,0,0,0,0] from first_two_basis 1,
      act,act,full_factor_action m u hu,full_factor_action m u hu,
      full_factor_action l t ht,full_factor_action l t ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The determinant of the quotient-plane action is the scalar on the first line. -/
theorem matrix_det (g : parabolic₂ (F := F)) :
    (longMatrix g.val).det = (scalarHom g : F) := by
  obtain ⟨l,t,M,ht,hg⟩ := long_factor g
  rw [scalar_factor l t ht M g hg, hg, matrix_factor l t ht]
  have hm := M.property
  rw [Matrix.det_fin_two] at hm
  simp only [Matrix.det_fin_two_of]
  linear_combination (l : F) * hm

/-- Its line-scalar kernel is exactly the vector-fixing local subgroup. -/
theorem scalar_eq_one_iff (g : parabolic₂ (F := F)) :
    scalarHom g = 1 ↔ g.val ∈ local₂ := by
  change lineScalarHom ((MulEquiv.subgroupCongr parabolic_eq_pointStabilizer) g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, lineScalarHom_kernel]
  change g.val ∈ fixingFirstVector ↔ g.val ∈ local₂
  rw [local₂_eq_fixingFirstVector]

variable [Finite F]

private noncomputable def normalizingScalar : parabolic₂ (F := F) →* F :=
  (frobeniusEquiv F 2).symm.toMonoidHom.comp
    ((Units.coeHom F).comp (scalarHom (F := F))⁻¹)

private theorem normalizingScalar_sq (g : parabolic₂ (F := F)) :
    normalizingScalar g ^ 2 = (scalarHom g : F)⁻¹ :=
  frobeniusEquiv_symm_pow_p F 2 _

private theorem normalizingScalar_of_local (g : local₂ (F := F)) :
    normalizingScalar ⟨g.val, local₂_le_parabolic₂ g.property⟩ = 1 := by
  have hs := (scalar_eq_one_iff ⟨g.val, local₂_le_parabolic₂ g.property⟩).mpr g.property
  change (frobeniusEquiv F 2).symm (↑(scalarHom ⟨g.val, local₂_le_parabolic₂ g.property⟩)⁻¹) = 1
  rw [hs]
  simp

/-- Normalize the genuine quotient-plane action by the inverse square root
of its determinant. This includes the torus of the full parabolic. -/
noncomputable def fullSLHom : parabolic₂ (F := F) →* SL(2,F) where
  toFun g := ⟨normalizingScalar g • longMatrix g.val, by
    rw [Matrix.det_smul, Fintype.card_fin, normalizingScalar_sq, matrix_det]
    exact inv_mul_cancel₀ (Units.ne_zero _)⟩
  map_one' := by
    apply Subtype.ext
    change normalizingScalar 1 • longMatrix 1 = _
    rw [map_one,one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [longMatrix,E,basisVector]
  map_mul' g h := by
    apply Subtype.ext
    change normalizingScalar (g*h) • longMatrix (g.val*h.val) =
      (normalizingScalar g • longMatrix g.val) * (normalizingScalar h • longMatrix h.val)
    rw [map_mul,matrix_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]

/-- On the local subgroup, normalization is trivial and recovers the existing map. -/
theorem fullSLHom_local (g : local₂ (F := F)) :
    fullSLHom ⟨g.val, local₂_le_parabolic₂ g.property⟩ = longSLHom g := by
  apply Subtype.ext
  change normalizingScalar ⟨g.val, local₂_le_parabolic₂ g.property⟩ • longMatrix g.val = _
  rw [normalizingScalar_of_local,one_smul]
  rfl

/-- The concrete block section proves surjectivity on the full parabolic. -/
theorem fullSLHom_surjective : Function.Surjective (fullSLHom (F := F)) := by
  intro M
  obtain ⟨g,hg⟩ := longSLHom_surjective M
  exact ⟨⟨g.val,local₂_le_parabolic₂ g.property⟩, (fullSLHom_local g).trans hg⟩

/-- The kernel is solvable: its scalar kernel embeds into the five-root two-group,
and its scalar image is abelian. -/
theorem fullSLHom_ker_isSolvable : Group.IsSolvable (fullSLHom (F := F)).ker := by
  let K := (fullSLHom (F := F)).ker
  let d : K →* Fˣ := scalarHom.comp K.subtype
  have hrad (x : d.ker) : x.val.val.val ∈ radical₂ := by
    have hs : scalarHom x.val.val = 1 := x.property
    have hl := (scalar_eq_one_iff x.val.val).mp hs
    let g : local₂ (F := F) := ⟨x.val.val.val,hl⟩
    have hg : longSLHom g = 1 := (fullSLHom_local g).symm.trans x.val.property
    have hk : g ∈ (longSLHom (F := F)).ker := hg
    rw [longSLHom_ker] at hk
    exact hk
  let k : d.ker →* radical₂ (F := F) :=
    ((parabolic₂.subtype.comp K.subtype).comp d.ker.subtype).codRestrict _ hrad
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : radical₂ (F := F) => r.val) h
  let : Group.IsNilpotent (radical₂ (F := F)) := radical₂_isTwoGroup.isNilpotent
  let : Group.IsSolvable d.ker := Group.isSolvable_of_isSolvable_injective hk
  exact Group.isSolvable_of_ker_le_range d.ker.subtype d (by
    rw [Subgroup.range_subtype])

private theorem field_parameter (hq : 2 < Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  have hc : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ha' : a ≠ 0 ∧ a ≠ 1 := by simpa using ha
  refine ⟨a,ha'.1,?_⟩
  intro h
  rcases sq_eq_one_iff.mp h with h | h
  · exact ha'.2 h
  · exact ha'.2 (by simpa only [CharTwo.neg_eq] using h)

private theorem sl_radical_eq_bot (hq : 2 < Nat.card F) :
    Subgroup.solvableRadical SL(2,F) = ⊥ := by
  let : IsSimpleGroup PSL(2,F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' (field_parameter hq)
  let : IsSimpleGroup SL(2,F) := (longSLEquivPSL (F := F)).isSimpleGroup
  obtain ⟨a,ha,ha2⟩ := field_parameter hq
  let : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top ha ha2⟩
  rcases (inferInstance : (Subgroup.solvableRadical SL(2,F)).Normal).eq_bot_or_eq_top
    with h | h
  · exact h
  · have hs : Group.IsSolvable (⊤ : Subgroup SL(2,F)) :=
      h ▸ Subgroup.solvableRadical_isSolvable (G := SL(2,F))
    let := hs
    have hs' : Group.IsSolvable SL(2,F) :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv :
        (⊤ : Subgroup SL(2,F)) ≃* SL(2,F)).toMonoidHom) Subgroup.topEquiv.surjective
    exact (Group.IsPerfect.not_isSolvable SL(2,F) hs').elim

/-- The normalized plane-action kernel is exactly the solvable radical of the
full parabolic, including the scalar torus contribution. -/
theorem fullSLHom_ker (hq : 2 < Nat.card F) :
    (fullSLHom (F := F)).ker = Subgroup.solvableRadical (parabolic₂ (F := F)) := by
  let := fullSLHom_ker_isSolvable (F := F)
  have h := Subgroup.comap_solvableRadical_eq_of_solvable_ker
    (fullSLHom (F := F)) fullSLHom_surjective
  simpa only [sl_radical_eq_bot hq, MonoidHom.comap_bot] using h

/-- The full long G₂ parabolic modulo its actual solvable radical is PSL₂(F). -/
noncomputable def parabolic₂RadicalQuotientEquivPSL (hq : 2 < Nat.card F) :
    parabolic₂ (F := F) ⧸ Subgroup.solvableRadical (parabolic₂ (F := F)) ≃* PSL(2,F) :=
  ((QuotientGroup.quotientMulEquivOfEq (fullSLHom_ker hq).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective fullSLHom fullSLHom_surjective)).trans
      longSLEquivPSL

end Atlas.G2.HigherParabolicRadical.Long
