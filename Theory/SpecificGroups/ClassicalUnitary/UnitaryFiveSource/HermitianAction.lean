module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.PlaneCenter
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Conjugation
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Residual
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import Theory.GroupTheory.Amalgam.LocalStructure
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Faithfulness

/-!
# The Hermitian action on the unitary-five plane-core center

The center parameters have zero vector coordinate and an arbitrary Hermitian
matrix coordinate. Entrywise field transport identifies their actual SL₂
conjugation action with the binary Hermitian module over GF(16). The same
construction on any group identified with the geometric plane semidirect
product retains the canonical two-core and the literal Levi projection.
Faithfulness proves that the center's centralizer inside that residual is
exactly its two-core. The Chapter6 companion applies these coordinates to
the original prepared residual and its ambient Thompson subgroup.

Source: Aschbacher–Smith F.4.29(6) and F.4.35, printed pp.289,292
(`refs/quasithin.pdf`). These are local action calculations, not an assertion
of the full ambient centralizer or the equality J(T)=Z(Q₂).
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore.Parameters
open Representation.OrthogonalFourMinus
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

omit [CharP F 2] in
theorem field_conjugation (hconj : ∀ a, J.conj a = a ^ 4)
    (e : F ≃+* FiniteModel.Field 2) (a : F) :
    e (J.conj a) = FiniteModel.conjugation 2 (e a) := by
  rw [hconj, map_pow]
  rfl

/-- Matrix entries identify the actual center with the Hermitian four-space. -/
def centerHermitianEquiv (c : F) (hc : c + J.conj c = 1)
    (hconj : ∀ a, J.conj a = a ^ 4) (e : F ≃+* FiniteModel.Field 2) :
    center (Parameters J) ≃* Multiplicative (FiniteModel.Space 2) where
  toFun u := Multiplicative.ofAdd ⟨u.val.z.map e, by
    ext i j
    change FiniteModel.conjugation 2 (e (u.val.z j i)) = e (u.val.z i j)
    rw [←field_conjugation J hconj e]
    apply congrArg e
    have hh := u.val.relation i j
    rw [(mem_center_iff_x_eq_zero J c hc u.val).mp u.property] at hh
    simp only [Pi.zero_apply, zero_mul] at hh
    exact add_left_cancel (hh.trans (CharTwo.add_self_eq_zero _).symm)⟩
  invFun v := ⟨⟨0,v.toAdd.val.map e.symm,by
    intro i j
    apply e.injective
    simp only [map_add, Matrix.map_apply, e.apply_symm_apply, Pi.zero_apply,
      zero_mul, map_zero, field_conjugation J hconj e]
    rw [FiniteModel.entry_conjugate]
    exact CharTwo.add_self_eq_zero _⟩,mem_center_of_x_eq_zero J _ rfl⟩
  left_inv u := by
    apply Subtype.ext
    apply Parameters.ext
    · exact ((mem_center_iff_x_eq_zero J c hc u.val).mp u.property).symm
    · ext i j
      exact e.symm_apply_apply _
  right_inv v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply _
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    ext i j
    change e (u.val.z i j + v.val.z i j + u.val.x i * J.conj (v.val.x j)) = _
    rw [(mem_center_iff_x_eq_zero J c hc u.val).mp u.property]
    simp

theorem centerHermitianEquiv_planeAction (c : F) (hc : c + J.conj c = 1)
    (hconj : ∀ a, J.conj a = a ^ 4) (e : F ≃+* FiniteModel.Field 2)
    (A : SpecialLinearGroup (Fin 2) F) (u : center (Parameters J)) :
    centerHermitianEquiv J c hc hconj e
      ((Subgroup.centerCongr (planeAction A)) u) =
      Multiplicative.ofAdd (Representation.SL2.BinarySmall.hermitian 2
        (SpecialLinearGroup.map e.toRingHom A)
        (centerHermitianEquiv J c hc hconj e u).toAdd) := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change (A.val * u.val.z * planeAdjoint J A.val).map e =
    A.val.map e * u.val.z.map e * adjoint (FiniteModel.conjugation 2) (A.val.map e)
  simp only [Matrix.map_mul]
  congr 1
  ext i j
  exact field_conjugation J hconj e _

end Theory.SpecificGroups.UnitaryFive.PlaneCore.Parameters

namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
open Subgroup
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- Central parameters are conjugated by the actual Levi projection. -/
theorem inl_center_conjugation (p : PlaneSemidirect J) (u : center (Parameters J)) :
    SemidirectProduct.inl ((centerCongr (Parameters.planeAction p.right)) u).val =
      p * SemidirectProduct.inl u.val * p⁻¹ := by
  conv_rhs => rw [←SemidirectProduct.inl_left_mul_inr_right p, _root_.mul_inv_rev]
  have hu := ((centerCongr (Parameters.planeAction p.right)) u).property
  change Parameters.planeAction p.right u.val ∈ center (Parameters J) at hu
  change (SemidirectProduct.inl (Parameters.planeAction p.right u.val) : PlaneSemidirect J) = _
  rw [show (SemidirectProduct.inl p.left * SemidirectProduct.inr p.right) *
      SemidirectProduct.inl u.val *
      ((SemidirectProduct.inr p.right)⁻¹ * (SemidirectProduct.inl p.left)⁻¹) =
      (SemidirectProduct.inl p.left *
        (SemidirectProduct.inr p.right * SemidirectProduct.inl u.val *
          SemidirectProduct.inr p.right⁻¹) * (SemidirectProduct.inl p.left)⁻¹ : PlaneSemidirect J) by
    simp only [map_inv]; group]
  rw [←SemidirectProduct.inl_aut, ←map_inv, ←map_mul, ←map_mul,
    (mem_center_iff.mp hu) p.left, mul_inv_cancel_right]

variable [Finite F]
private instance parametersFinite : Finite (Parameters J) :=
  Finite.of_injective (fun u : Parameters J => (u.x,u.z)) (by
    intro u v h
    exact Parameters.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

private instance semidirectFinite : Finite (PlaneSemidirect J) :=
  Finite.of_injective (fun p : PlaneSemidirect J => (p.left,p.right)) (by
    intro p q h
    exact SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- The kernel of the literal Levi projection is the canonical two-core. -/
theorem semidirect_pCore : pCore 2 (PlaneSemidirect J) =
    (SemidirectProduct.inl : Parameters J →* PlaneSemidirect J).range := by
  have hk : IsPGroup 2 (SemidirectProduct.rightHom : PlaneSemidirect J →*
      SpecialLinearGroup (Fin 2) F).ker := by
    rw [←SemidirectProduct.range_inl_eq_ker_rightHom]
    exact (Parameters.isPGroup (J := J)).of_surjective _
      (MonoidHom.rangeRestrict_surjective (SemidirectProduct.inl : Parameters J →* PlaneSemidirect J))
  have hh := (SemidirectProduct.rightHom : PlaneSemidirect J →*
      SpecialLinearGroup (Fin 2) F).comap_pCore_of_ker_isPGroup
    SemidirectProduct.rightHom_surjective hk
  rw [ResidualAction.sl_twoCore_eq_bot, MonoidHom.comap_bot,
    ←SemidirectProduct.range_inl_eq_ker_rightHom] at hh
  exact hh.symm

/-- Parameters of the canonical semidirect-product core. -/
def semidirectCoreEquiv : pCore 2 (PlaneSemidirect J) ≃* Parameters J :=
  (MulEquiv.subgroupCongr (semidirect_pCore J)).trans
    (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := Parameters.planeAction (J := J)))).symm

theorem inl_semidirectCoreEquiv (u : pCore 2 (PlaneSemidirect J)) :
    SemidirectProduct.inl (semidirectCoreEquiv J u) = u.val :=
  congrArg Subtype.val ((MonoidHom.ofInjective
    (SemidirectProduct.inl_injective (φ := Parameters.planeAction (J := J)))).apply_symm_apply
      ((MulEquiv.subgroupCongr (semidirect_pCore J)) u))

end Theory.SpecificGroups.UnitaryFive.PlaneCore

namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
open Subgroup Theory.GroupTheory Representation.OrthogonalFourMinus
variable {F R : Type*} [Field F] [CharP F 2] [Finite F]
  [Group R] (J : HermitianForm 5 F) (e : R ≃* PlaneSemidirect J)

def coreCoordinates : pCore 2 R ≃* Parameters J :=
  (LocalCoreTransport.coreEquiv 2 e).trans (semidirectCoreEquiv J)

theorem inl_coreCoordinates (u : pCore 2 R) :
    SemidirectProduct.inl (coreCoordinates J e u) = e u.val :=
  inl_semidirectCoreEquiv J (LocalCoreTransport.coreEquiv 2 e u)

/-- The center coordinates intertwine conjugation and the native Levi action. -/
theorem coreCoordinates_center_conjugation (r : R) (u : center (pCore 2 R)) :
    coreCoordinates J e (MulAut.conjNormal r u.val) =
      Parameters.planeAction (e r).right (coreCoordinates J e u.val) := by
  apply SemidirectProduct.inl_injective (φ := Parameters.planeAction (J := J))
  rw [inl_coreCoordinates]
  have hh := inl_center_conjugation J (e r) ((centerCongr (coreCoordinates J e)) u)
  change (SemidirectProduct.inl
      (Parameters.planeAction (e r).right (coreCoordinates J e u.val)) : PlaneSemidirect J) =
    e r * SemidirectProduct.inl (coreCoordinates J e u.val) * (e r)⁻¹ at hh
  rw [inl_coreCoordinates] at hh
  rw [hh]
  change e (r * u.val.val * r⁻¹) = _
  simp only [map_mul,map_inv]

/-- Coordinates of the full center of the canonical two-core. -/
def coreCenterHermitianEquiv (c : F) (hc : c + J.conj c = 1)
    (hconj : ∀ a, J.conj a = a ^ 4) (b : F ≃+* FiniteModel.Field 2) :
    center (pCore 2 R) ≃* Multiplicative (FiniteModel.Space 2) :=
  (centerCongr (coreCoordinates J e)).trans
    (Parameters.centerHermitianEquiv J c hc hconj b)

/-- The genuine SL₂ quotient map of the given residual coordinates. -/
def hermitianProjection (b : F ≃+* FiniteModel.Field 2) :
    R →* SpecialLinearGroup (Fin 2) (FiniteModel.Field 2) :=
  (Theory.PSL2.OuterSolvable.slRingEquiv b).toMonoidHom.comp
    (SemidirectProduct.rightHom.comp e.toMonoidHom)

omit [Finite F] in
theorem hermitianProjection_surjective (b : F ≃+* FiniteModel.Field 2) :
    Function.Surjective (hermitianProjection J e b) :=
  (Theory.PSL2.OuterSolvable.slRingEquiv b).surjective.comp
    (SemidirectProduct.rightHom_surjective.comp e.surjective)

theorem hermitianProjection_ker (b : F ≃+* FiniteModel.Field 2) :
    (hermitianProjection J e b).ker = pCore 2 R := by
  ext r
  change (Theory.PSL2.OuterSolvable.slRingEquiv b) (e r).right = 1 ↔ r ∈ pCore 2 R
  rw [←(Theory.PSL2.OuterSolvable.slRingEquiv b).map_one,
    (Theory.PSL2.OuterSolvable.slRingEquiv b).injective.eq_iff]
  change e r ∈ (SemidirectProduct.rightHom : PlaneSemidirect J →*
    SpecialLinearGroup (Fin 2) F).ker ↔ _
  rw [←SemidirectProduct.range_inl_eq_ker_rightHom, ←semidirect_pCore J,
    ←pCore_map_iso 2 e]
  exact mem_map_iff_mem (f := e.toMonoidHom) e.injective

/-- All elements of the residual act through the same canonical quotient. -/
theorem coreCenterHermitianEquiv_conjugation (c : F) (hc : c + J.conj c = 1)
    (hconj : ∀ a, J.conj a = a ^ 4) (b : F ≃+* FiniteModel.Field 2)
    (r : R) (u : center (pCore 2 R)) :
    coreCenterHermitianEquiv J e c hc hconj b
      ((centerCongr (MulAut.conjNormal r)) u) =
      Multiplicative.ofAdd (Representation.SL2.BinarySmall.hermitian 2
        (hermitianProjection J e b r)
        (coreCenterHermitianEquiv J e c hc hconj b u).toAdd) := by
  change Parameters.centerHermitianEquiv J c hc hconj b
      ((centerCongr (coreCoordinates J e)) ((centerCongr (MulAut.conjNormal r)) u)) = _
  rw [show (centerCongr (coreCoordinates J e)) ((centerCongr (MulAut.conjNormal r)) u) =
      (centerCongr (Parameters.planeAction (e r).right)) ((centerCongr (coreCoordinates J e)) u)
    from Subtype.ext (coreCoordinates_center_conjugation J e r u)]
  exact Parameters.centerHermitianEquiv_planeAction J c hc hconj b _ _

end Theory.SpecificGroups.UnitaryFive.PlaneCore

namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
open Subgroup Theory.GroupTheory Representation.OrthogonalFourMinus
variable {F R : Type*} [Field F] [CharP F 2] [Finite F]
  [Group R] (J : HermitianForm 5 F) (e : R ≃* PlaneSemidirect J)

include e in
/-- Inside the actual residual, the full core-center centralizer is the two-core. -/
theorem centralizer_coreCenter (c : F) (hc : c + J.conj c = 1)
    (hconj : ∀ a, J.conj a = a ^ 4) (b : F ≃+* FiniteModel.Field 2) :
    centralizer ((center (pCore 2 R)).map (pCore 2 R).subtype : Set R) = pCore 2 R := by
  let f := coreCenterHermitianEquiv J e c hc hconj b
  apply le_antisymm
  · intro r hr
    have hu (u : center (pCore 2 R)) : (centerCongr (MulAut.conjNormal r)) u = u := by
      apply Subtype.ext
      apply Subtype.ext
      change r * u.val.val * r⁻¹ = u.val.val
      rw [←hr u.val.val ⟨u.val,u.property,rfl⟩,mul_inv_cancel_right]
    have ha : FiniteModel.action 2 (hermitianProjection J e b r) = FiniteModel.action 2 1 := by
      apply LinearMap.ext
      intro v
      obtain ⟨u,he⟩ := f.surjective (Multiplicative.ofAdd v)
      have hh := coreCenterHermitianEquiv_conjugation J e c hc hconj b r u
      change f ((centerCongr (MulAut.conjNormal r)) u) = _ at hh
      rw [hu] at hh
      change f u = Multiplicative.ofAdd
        (Representation.SL2.BinarySmall.hermitian 2 (hermitianProjection J e b r) (f u).toAdd) at hh
      rw [he] at hh
      have hh' := congrArg Multiplicative.toAdd hh
      rw [map_one]
      apply Subtype.ext
      exact congrArg (fun v : FiniteModel.Space 2 => v.val) hh'.symm
    have hk : r ∈ (hermitianProjection J e b).ker := FiniteModel.action_injective 2 ha
    rwa [hermitianProjection_ker] at hk
  · intro r hr z hz
    obtain ⟨z,hz,rfl⟩ := hz
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨r,hr⟩).symm

end Theory.SpecificGroups.UnitaryFive.PlaneCore
