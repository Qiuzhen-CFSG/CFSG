module

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Borel
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The full short G₂ parabolic modulo its solvable radical

The full short parabolic acts on its standard null plane. Over a finite field
of characteristic two, the inverse Frobenius gives a multiplicative square
root of the determinant. Dividing the plane action by that scalar gives an
actual surjective homomorphism to SL₂: on the short local subgroup it is the
previously constructed rank-one quotient map.

An element in the kernel acts as a scalar on the plane. It therefore fixes
its first projective point and lies in the intersection of the two full
parabolics, namely the solvable Borel. Thus the kernel is solvable. For q > 2,
SL₂ is nonabelian simple, so this kernel is exactly the full parabolic's
solvable radical. This includes the scalar torus contribution, as well as the
five-root unipotent radical. The trivial center of SL₂ gives the final PSL₂
identification.

Source: Aschbacher--Smith, E.1.14(1), printed p.214, and the rank-one
parabolic structure in F.1.12(I)(3), printed pp.262--264. The octonion model,
root coordinates and geometric parabolics use the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open scoped MatrixGroups
open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion Atlas.G2.LieParabolicSetup

namespace Atlas.G2.HigherParabolicRadical.Short
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private noncomputable def rootDet (g : shortPlaneStabilizer (F := F)) : F :=
  (frobeniusEquiv F 2).symm (shortDet g)

private theorem rootDet_sq (g : shortPlaneStabilizer (F := F)) :
    rootDet g ^ 2 = shortDet g :=
  (frobeniusEquiv F 2).apply_symm_apply _

private theorem rootDet_ne_zero (g : shortPlaneStabilizer (F := F)) :
    rootDet g ≠ 0 := by
  apply (map_ne_zero (frobeniusEquiv F 2).symm).mpr
  exact (isUnit_iff_ne_zero).mp ((Group.isUnit g).map shortDet)

private noncomputable def normalizedPlaneHom : shortPlaneStabilizer (F := F) →* SL(2,F) where
  toFun g := ⟨(rootDet g)⁻¹ • shortRepresentation g, by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, rootDet_sq]
    exact inv_mul_cancel₀ ((isUnit_iff_ne_zero).mp ((Group.isUnit g).map shortDet))⟩
  map_one' := by
    apply Subtype.ext
    simp [rootDet]
  map_mul' g h := by
    apply Subtype.ext
    change (rootDet (g*h))⁻¹ • shortRepresentation (g*h) =
      ((rootDet g)⁻¹ • shortRepresentation g) * ((rootDet h)⁻¹ • shortRepresentation h)
    simp [rootDet, map_mul, smul_smul]

private theorem ker_mem_borel (g : shortPlaneStabilizer (F := F))
    (hg : normalizedPlaneHom g = 1) : g.val ∈ borel := by
  have he : shortRepresentation g = rootDet g • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => rootDet g • A)
      (congrArg Subtype.val hg)
    change rootDet g • ((rootDet g)⁻¹ • shortRepresentation g) =
      rootDet g • (1 : Matrix (Fin 2) (Fin 2) F) at h
    simpa only [smul_smul, mul_inv_cancel₀ (rootDet_ne_zero g), one_smul] using h
  have h0 : g.val.val (basisVector 0) 0 = rootDet g := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 0) he
    change g.val.val (basisVector 0) 0 = (rootDet g • (1 : Matrix (Fin 2) (Fin 2) F)) 0 0 at h
    simpa using h
  have h1 : g.val.val (basisVector 0) 1 = 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 1 0) he
    change g.val.val (basisVector 0) 1 = (rootDet g • (1 : Matrix (Fin 2) (Fin 2) F)) 1 0 at h
    simpa using h
  have hf : g.val.val (basisVector 0) = rootDet g • basisVector 0 := by
    rw [shortPlane_coordinates (g.property.1 _ (basis_mem_shortPlane 0 (by decide))), h0, h1]
    funext i
    fin_cases i <;> simp [basisVector]
  have hp : g.val ∈ parabolic₂ := by
    change g.val ∈ parabolic
    rw [parabolic_eq_pointStabilizer]
    exact (mem_pointStabilizer_iff _).mpr ⟨Units.mk0 _ (rootDet_ne_zero g), hf⟩
  exact shortPlaneStabilizer_inf_parabolic₂.le ⟨g.property, hp⟩

/-- The determinant-normalized plane action of the full short parabolic. -/
noncomputable def fullSLHom : parabolic₁ (F := F) →* SL(2,F) :=
  normalizedPlaneHom.comp (Subgroup.inclusion parabolic₁_le_shortPlaneStabilizer)

omit [Finite F] [CharP F 2] in
private theorem local_le_full : local₁ (F := F) ≤ parabolic₁ := by
  rw [← local₁_sup_borel]
  exact le_sup_left

private theorem fullSLHom_local (g : local₁ (F := F)) :
    fullSLHom ⟨g.val, local_le_full g.property⟩ = shortSLHom g := by
  apply Subtype.ext
  change (rootDet ⟨g.val, _⟩)⁻¹ • (shortSLHom g).val = (shortSLHom g).val
  have hd : shortDet ⟨g.val, parabolic₁_le_shortPlaneStabilizer
      (local_le_full g.property)⟩ = 1 := (shortSLHom g).property
  simp [rootDet, hd]

/-- The existing local rank-one map supplies every determinant-one matrix. -/
theorem fullSLHom_surjective : Function.Surjective (fullSLHom (F := F)) := by
  intro A
  obtain ⟨g, rfl⟩ := shortSLHom_surjective A
  exact ⟨⟨g.val, local_le_full g.property⟩, fullSLHom_local g⟩

private theorem ker_le_borel : (fullSLHom (F := F)).ker ≤
    (borel (K := F)).subgroupOf parabolic₁ := by
  intro g hg
  exact ker_mem_borel ⟨g.val, parabolic₁_le_shortPlaneStabilizer g.property⟩ hg

/-- The scalar-action kernel embeds in the solvable Borel. -/
theorem fullSLHom_ker_solvable : Group.IsSolvable (fullSLHom (F := F)).ker := by
  let : Group.IsSolvable (borel (K := F)) := DerivedNormalizerSolvable.isSolvable_borel
  let e := Subgroup.subgroupOfEquivOfLe (borel_le_parabolic₁ (F := F))
  let : Group.IsSolvable ((borel (K := F)).subgroupOf parabolic₁) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (ker_le_borel (F := F))) (Subgroup.inclusion_injective _)

private theorem sl_radical_eq_bot (hq : 2 < Nat.card F) :
    Subgroup.solvableRadical SL(2,F) = ⊥ := by
  classical
  let := Fintype.ofFinite F
  have hc : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ha' : a ≠ 0 ∧ a ≠ 1 := by simpa using ha
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h | h
    · exact ha'.2 h
    · exact ha'.2 (by simpa only [CharTwo.neg_eq] using h)
  let : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top ha'.1 ha2⟩
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'
    ⟨a, ha'.1, ha2⟩
  let : IsSimpleGroup SL(2,F) := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup
  rcases (inferInstance : (Subgroup.solvableRadical SL(2,F)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let : Group.IsSolvable (⊤ : Subgroup SL(2,F)) := h ▸ inferInstanceAs
      (Group.IsSolvable (Subgroup.solvableRadical SL(2,F)))
    exact (Group.IsPerfect.not_isSolvable SL(2,F)
      (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := SL(2,F))).toMonoidHom)
        (Subgroup.topEquiv (G := SL(2,F))).surjective)).elim

/-- The exact kernel is the intrinsic solvable radical of the full parabolic. -/
theorem fullSLHom_ker_eq_solvableRadical (hq : 2 < Nat.card F) :
    (fullSLHom (F := F)).ker = Subgroup.solvableRadical (parabolic₁ (F := F)) := by
  let : Group.IsSolvable (fullSLHom (F := F)).ker := fullSLHom_ker_solvable
  have h := Subgroup.comap_solvableRadical_eq_of_solvable_ker
    (fullSLHom (F := F)) fullSLHom_surjective
  rw [sl_radical_eq_bot hq] at h
  exact h

/-- The actual full short parabolic modulo its solvable radical is PSL₂. -/
noncomputable def parabolic₁RadicalQuotientEquivPSL (hq : 2 < Nat.card F) :
    parabolic₁ (F := F) ⧸ Subgroup.solvableRadical (parabolic₁ (F := F)) ≃* PSL(2,F) :=
  (QuotientGroup.liftEquiv _ fullSLHom_surjective
    (fullSLHom_ker_eq_solvableRadical hq).symm).trans Atlas.RankOneFieldAutomorphisms.slEquivPSL

/-- On representatives, the equivalence is the normalized plane action followed
by the canonical central quotient. -/
@[simp] theorem parabolic₁RadicalQuotientEquivPSL_mk (hq : 2 < Nat.card F)
    (g : parabolic₁ (F := F)) :
    parabolic₁RadicalQuotientEquivPSL hq (QuotientGroup.mk g) =
      QuotientGroup.mk (fullSLHom g) := by
  exact congrArg (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F))
    (QuotientGroup.liftEquiv_mk _ fullSLHom_surjective
      (fullSLHom_ker_eq_solvableRadical hq).symm g)

end Atlas.G2.HigherParabolicRadical.Short
