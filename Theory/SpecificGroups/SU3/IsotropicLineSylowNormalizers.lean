module

public import BenderSuzuki.SE.Borel
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.Geometry
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# Isotropic-line stabilizers are Sylow two-normalizers in SU₃ and PSU₃

The standard Hermitian action identifies one isotropic-line stabilizer with
a Sylow normalizer. Transitivity and conjugation give every isotropic line.
For an arbitrary form, an actual Hermitian basis change transports both the
line and its matrix stabilizer. The special-unitary result follows by taking
inverse images through SU₃ → PSU₃, whose kernel is central.

The two finite-field cardinalities and the original form are retained. These
are intrinsic matrix-group results used to convert geometric no-Borel
conditions into exclusion from Sylow normalizers.

Source: GLS4, Chapter 4, Lemmas 3.2(a–c) and 3.11; Huppert II.10.4 and II.10.12.
-/

noncomputable section
open Matrix Subgroup BenderSuzuki BenderSuzuki.MatrixGroups
open scoped LinearAlgebra.Projectivization
namespace UnitaryThree.OddTorusNormalizer.IsotropicSylow
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {E : Type*} [Field E] [Finite E]

private instance : Finite (ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

omit [Finite E] in
private theorem toLin_smul (A : GL (Fin 3) E) (l : ℙ E (Fin 3 → E)) :
    (GeneralLinearGroup.toLin A).toLinearEquiv • l = A • l := by
  induction l using Projectivization.ind with
  | _ v hv =>
    rw [Projectivization.smul_mk, Projectivization.smul_mk]
    rfl

private theorem standard_stabilizer (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hc : Nat.card E = (2^n)^2) (hf : Nat.card {x : E // J.conj x = x} = 2^n)
    (l : ℙ E (Fin 3 → E)) (hl : IsIsotropicLine J l) :
    ∃ P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) l = normalizer (P : Set _) := by
  let Omega := {l : ℙ E (Fin 3 → E) // IsIsotropicLine J l}
  obtain ⟨rho, alpha, S, _, hnatural, _, hN, _, htwo⟩ :=
    psu_sylow_normalizer_action J n hn hc hf hJ
  have hact (g : ProjectiveSpecialUnitaryMatrixGroup J) (z : Omega) :
      (rho g z).val = g • z.val := by
    obtain ⟨x, rfl⟩ := J.specialToProjective_surjective g
    have hh := hnatural (J.specialToProjective x) z x (J.specialToProjective_apply_val x).symm
    rw [specialToProjective_smul]
    exact hh.trans (toLin_smul x.val z.val)
  have hNa : normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) alpha.val := by
    change normalizer ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = _
    rw [hN]
    ext g
    change rho g alpha = alpha ↔ g • alpha.val = alpha.val
    constructor
    · intro he
      exact (hact g alpha).symm.trans (congrArg Subtype.val he)
    · intro he
      exact Subtype.ext ((hact g alpha).trans he)
  obtain ⟨g, hg⟩ : ∃ g, rho g alpha = (⟨l, hl⟩ : Omega) := by
    by_cases he : alpha = (⟨l, hl⟩ : Omega)
    · exact ⟨1, by simpa using he⟩
    · obtain ⟨g, hg, _⟩ := htwo alpha ⟨l, hl⟩ ⟨l, hl⟩ alpha he (Ne.symm he)
      exact ⟨g, hg⟩
  refine ⟨S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective, ?_⟩
  have hgl : g • alpha.val = l := (hact g alpha).symm.trans (congrArg Subtype.val hg)
  rw [← hgl, MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← hNa]
  exact map_equiv_normalizer_eq (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (MulAut.conj g)

omit [Finite E] in
private theorem hermitian_basis_value (J : HermitianForm 3 E) (C : GL (Fin 3) E)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (v : Fin 3 → E) :
    dotProduct (fun i => (standardForm J).conj (v i)) ((standardForm J).form.mulVec v) =
      dotProduct (fun i => J.conj ((C.val.mulVec v) i)) (J.form.mulVec (C.val.mulVec v)) := by
  rw [← hC]
  simp only [← Matrix.mulVec_mulVec]
  change dotProduct (fun i => J.conj (v i))
    ((C.val.map J.conj).transpose.mulVec (J.form.mulVec (C.val.mulVec v))) = _
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  congr 1
  ext i
  exact (RingHom.map_mulVec (J.conj : E →+* E) C.val v i).symm

omit [Finite E] in
private theorem isotropic_basis (J : HermitianForm 3 E) (C : GL (Fin 3) E)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (l : ℙ E (Fin 3 → E)) (hl : IsIsotropicLine J l) :
    IsIsotropicLine (standardForm J) ((ProjGenLinGroup.mk C)⁻¹ • l) := by
  obtain ⟨v, hv, rfl, hiso⟩ := hl
  let w := C⁻¹ • v
  have hw : w ≠ 0 := (smul_ne_zero_iff_ne _).mpr hv
  refine ⟨w, hw, ?_, ?_⟩
  · rw [← map_inv, Projectivization.PGL.mk_smul_mk]
  · rw [hermitian_basis_value J C hC]
    have hCv : C.val.mulVec w = v := by
      change C • (C⁻¹ • v) = v
      exact smul_inv_smul C v
    rw [hCv]
    exact hiso

/-- Every actual isotropic-line stabilizer in PSU₃ is a Sylow two-normalizer,
including for an arbitrary nondegenerate Hermitian Gram matrix. -/
public theorem projective_stabilizer (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card E = (2^n)^2) (hf : Nat.card {x : E // J.conj x = x} = 2^n)
    (l : ℙ E (Fin 3 → E)) (hl : IsIsotropicLine J l) :
    ∃ P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) l = normalizer (P : Set _) := by
  obtain ⟨C, hC⟩ := exists_standard_basis J (2^n) hc hf
  let e := projectiveEquiv J C hC
  let l' := (ProjGenLinGroup.mk C)⁻¹ • l
  obtain ⟨S, hS⟩ := standard_stabilizer (standardForm J) hn rfl hc hf l'
    (isotropic_basis J C hC l hl)
  let P := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨P, ?_⟩
  have he : MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) l =
      (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) l').comap
        e.toMonoidHom := by
    ext g
    change g.val • l = l ↔ (e g).val • l' = l'
    rw [projectiveEquiv_apply]
    dsimp only [l']
    simp only [mul_smul, smul_inv_smul]
    exact (smul_left_cancel_iff _).symm
  rw [he, hS]
  change _ = normalizer ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup (standardForm J))).map e.symm.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  rw [← map_equiv_normalizer_eq, map_equiv_eq_comap_symm']
  rfl

/-- SU₃ retains the full scalar kernel in each isotropic-line stabilizer. -/
public theorem special_stabilizer (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card E = (2^n)^2) (hf : Nat.card {x : E // J.conj x = x} = 2^n)
    (l : ℙ E (Fin 3 → E)) (hl : IsIsotropicLine J l) :
    ∃ P : Sylow 2 J.specialSubgroup,
      MulAction.stabilizer J.specialSubgroup l = normalizer (P : Set _) := by
  obtain ⟨Q, hQ⟩ := projective_stabilizer J hn hc hf l hl
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective J.specialToProjective_surjective 2 Q
  refine ⟨P, ?_⟩
  have he : MulAction.stabilizer J.specialSubgroup l =
      (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) l).comap
        J.specialToProjective := by
    ext x
    change x • l = l ↔ J.specialToProjective x • l = l
    rw [specialToProjective_smul]
  rw [he, hQ]
  exact P.normalizer_comap_of_central_kernel J.specialToProjective
    J.specialToProjective_surjective J.specialToProjective_ker_le_center

end UnitaryThree.OddTorusNormalizer.IsotropicSylow
