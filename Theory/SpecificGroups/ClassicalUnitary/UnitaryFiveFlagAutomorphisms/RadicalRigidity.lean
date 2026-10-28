module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.HermitianAction
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# Vector and center rigidity for quotient-trivial residual actors

Restrict an actual residual automorphism to its characteristic two-core. An
actor trivial on SL₂ acts equivariantly on the radical vector quotient,
even when it moves the chosen Levi complement. The natural SL₂ commutant
therefore gives a nonzero field scalar. Explicit commutator generation
forces its norm scalar on the whole center. The full residual formula and
nonabelian Levi cocycle retain the remaining compatibility obligation.

Source: the coordinate reconstruction for Aschbacher–Smith F.4.29(2),
printed p.289 of refs/quasithin.pdf. These results alone do not give whole
radical or opposite-endpoint rigidity.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
open PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- The vector quotient is the quotient by the entire radical center. -/
def vectorQuotientEquiv (c : F) (hc : c + J.conj c = 1) :
    Parameters J ⧸ center (Parameters J) ≃* Multiplicative (Fin 2 → F) :=
  (QuotientGroup.quotientMulEquivOfEq (Parameters.center_eq_vector_ker J c hc)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (Parameters.vectorHom J)
      (Parameters.vectorHom_surjective J c hc))

@[simp] theorem vectorQuotientEquiv_mk (c : F) (hc : c + J.conj c = 1) (u : Parameters J) :
    vectorQuotientEquiv J c hc (QuotientGroup.mk' _ u) = Multiplicative.ofAdd u.x := rfl

def vectorAction (c : F) (hc : c + J.conj c = 1) (a : MulAut (Parameters J)) :
    MulAut (Multiplicative (Fin 2 → F)) :=
  MulAut.congr (vectorQuotientEquiv J c hc) (quotientAut (center (Parameters J)) a)

theorem vectorAction_apply (c : F) (hc : c + J.conj c = 1) (a : MulAut (Parameters J))
    (u : Parameters J) : vectorAction J c hc a (Multiplicative.ofAdd u.x) =
      Multiplicative.ofAdd (a u).x := by
  rw [←vectorQuotientEquiv_mk J c hc]
  change vectorQuotientEquiv J c hc
    (quotientAut _ a ((vectorQuotientEquiv J c hc).symm
      (vectorQuotientEquiv J c hc (QuotientGroup.mk' _ u)))) = _
  rw [MulEquiv.symm_apply_apply,quotientAut_apply_mk,vectorQuotientEquiv_mk]

private def vectorAddAction (c : F) (hc : c + J.conj c = 1) (a : MulAut (Parameters J)) :
    (Fin 2 → F) →+ (Fin 2 → F) where
  toFun v := (vectorAction J c hc a (Multiplicative.ofAdd v)).toAdd
  map_zero' := congrArg Multiplicative.toAdd (map_one (vectorAction J c hc a))
  map_add' v w := congrArg Multiplicative.toAdd
    (map_mul (vectorAction J c hc a) (Multiplicative.ofAdd v) (Multiplicative.ofAdd w))

private theorem radical_conjugation_x (v u : Parameters J) :
    (v * u * v⁻¹).x = u.x := by
  ext i
  simp only [Parameters.mul_x,Parameters.inv_x,Pi.add_apply]
  rw [add_right_comm,CharTwo.add_self_eq_zero,zero_add]

/-- Conjugation on the vector quotient only sees the actual Levi projection. -/
theorem semidirect_conjugation_x (p : PlaneSemidirect J) (u : Parameters J) :
    (p * SemidirectProduct.inl u * p⁻¹).left.x = p.right.val *ᵥ u.x := by
  have he : p * SemidirectProduct.inl u * p⁻¹ =
      SemidirectProduct.inl (p.left * Parameters.planeAction p.right u * p.left⁻¹) := by
    calc
      _ = SemidirectProduct.inl p.left *
          (SemidirectProduct.inr p.right * SemidirectProduct.inl u *
            (SemidirectProduct.inr p.right)⁻¹) * (SemidirectProduct.inl p.left)⁻¹ := by
        conv_lhs => rw [←SemidirectProduct.inl_left_mul_inr_right p]
        group
      _ = _ := by rw [←map_inv,←SemidirectProduct.inl_aut]; simp only [map_mul,map_inv,mul_assoc]
  rw [he]
  exact (radical_conjugation_x J p.left _).trans (Parameters.planeAction_x _ _)


open scoped commutatorElement in
private theorem commutator_z (u v : Parameters J) (i j : Fin 2) :
    ⁅u,v⁆.z i j = u.x i * J.conj (v.x j) + v.x i * J.conj (u.x j) := by
  simp only [commutatorElement_def, Parameters.mul_z, Parameters.mul_x,
    Parameters.inv_x, Parameters.inv_z, Pi.add_apply]
  linear_combination (u.z i j + v.z i j + u.x i * J.conj (u.x j) +
    v.x i * J.conj (v.x j) + u.x i * J.conj (v.x j)) * (CharTwo.two_eq_zero : (2 : F) = 0)

open scoped commutatorElement in
private theorem commutator_x (u v : Parameters J) : ⁅u,v⁆.x = 0 := by
  ext i
  simp only [commutatorElement_def, Parameters.mul_x, Parameters.inv_x,Pi.add_apply,Pi.zero_apply]
  linear_combination (u.x i + v.x i) * (CharTwo.two_eq_zero : (2 : F) = 0)

/-- The vector scalar forces the norm scalar on the entire center, by the
explicit three-commutator generation of that center. -/
theorem radical_center_scalar (c : F) (hc : c + J.conj c = 1)
    (a : MulAut (Parameters J)) (k : F) (hk : ∀ u, (a u).x = k • u.x)
    (u : Parameters J) (hu : u.x = 0) :
    (a u).z = (k * J.conj k) • u.z := by
  obtain ⟨v,w,r,s,t,y,rfl⟩ := Parameters.vector_zero_eq_commutator_product J c hc u hu
  simp only [map_mul,map_commutatorElement]
  ext i j
  simp only [Parameters.mul_z,Parameters.mul_x,commutator_x,Pi.zero_apply,Pi.add_apply,
    zero_mul,add_zero,Matrix.smul_apply,smul_eq_mul,commutator_z,hk,Pi.smul_apply,map_mul]
  ring

variable [Finite F]

/-- The actual residual actor restricted to its characteristic two-core. -/
def radicalAction (a : MulAut (PlaneSemidirect J)) : MulAut (Parameters J) :=
  MulAut.congr (semidirectCoreEquiv J) ((MulAut.characteristic (pCore 2 (PlaneSemidirect J))) a)

theorem radicalAction_inl (a : MulAut (PlaneSemidirect J)) (u : Parameters J) :
    SemidirectProduct.inl (radicalAction J a u) = a (SemidirectProduct.inl u) := by
  obtain ⟨v,rfl⟩ := (semidirectCoreEquiv J).surjective u
  change SemidirectProduct.inl (semidirectCoreEquiv J
    ((MulAut.characteristic _ a) ((semidirectCoreEquiv J).symm (semidirectCoreEquiv J v)))) = _
  rw [MulEquiv.symm_apply_apply,inl_semidirectCoreEquiv,inl_semidirectCoreEquiv]
  rfl

/-- Quotient-triviality implies equivariance on the vector quotient even when
 the chosen Levi complement is moved by the automorphism. -/
theorem radicalAction_vector_equivariant (a : MulAut (PlaneSemidirect J))
    (ha : ∀ p, (a p).right = p.right) (A : SpecialLinearGroup (Fin 2) F) (u : Parameters J) :
    (radicalAction J a (Parameters.planeAction A u)).x =
      A.val *ᵥ (radicalAction J a u).x := by
  have he : SemidirectProduct.inl (radicalAction J a (Parameters.planeAction A u)) =
      a (SemidirectProduct.inr A) * SemidirectProduct.inl (radicalAction J a u) *
        (a (SemidirectProduct.inr A))⁻¹ := by
    rw [radicalAction_inl,SemidirectProduct.inl_aut,map_mul,map_mul,map_inv,radicalAction_inl]
    simp only [map_inv]
  have hh := congrArg (fun p : PlaneSemidirect J => p.left.x) he
  rw [semidirect_conjugation_x,ha] at hh
  exact hh

/-- A residual actor trivial on SL₂ scales the entire natural vector quotient
by one nonzero field scalar. -/
theorem radicalAction_vector_scalar (c : F) (hc : c + J.conj c = 1)
    (a : MulAut (PlaneSemidirect J)) (ha : ∀ p, (a p).right = p.right) :
    ∃ k : F, k ≠ 0 ∧ ∀ u : Parameters J, (radicalAction J a u).x = k • u.x := by
  let b := radicalAction J a
  have he (A : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
      vectorAddAction J c hc b (A.val *ᵥ v) = A.val *ᵥ vectorAddAction J c hc b v := by
    obtain ⟨u,hu⟩ := Parameters.vectorHom_surjective J c hc (Multiplicative.ofAdd v)
    have hv : u.x = v := congrArg Multiplicative.toAdd hu
    rw [←hv,←Parameters.planeAction_x]
    change (vectorAction J c hc b (Multiplicative.ofAdd (Parameters.planeAction A u).x)).toAdd =
      A.val *ᵥ (vectorAction J c hc b (Multiplicative.ofAdd u.x)).toAdd
    rw [vectorAction_apply,vectorAction_apply]
    exact radicalAction_vector_equivariant J a ha A u
  obtain ⟨k,hk⟩ := Representation.SL2NaturalOffenders.centralizer_scalar
    (vectorAddAction J c hc b) he
  refine ⟨k,?_,?_⟩
  · intro hz
    have hv := hk ![1,0]
    rw [hz,zero_smul] at hv
    have hh : vectorAction J c hc b (Multiplicative.ofAdd ![1,0]) = 1 :=
      congrArg Multiplicative.ofAdd hv
    have hh := (vectorAction J c hc b).injective (hh.trans (map_one _).symm)
    have hh := congrArg (fun v : Multiplicative (Fin 2 → F) => v.toAdd 0) hh
    exact one_ne_zero hh
  · intro u
    have hh := hk u.x
    change (vectorAction J c hc b (Multiplicative.ofAdd u.x)).toAdd = _ at hh
    rwa [vectorAction_apply] at hh

/-- The actual displacement of the chosen Levi section. -/
def leviDeviation (a : MulAut (PlaneSemidirect J)) (A : SpecialLinearGroup (Fin 2) F) :
    Parameters J := (a (SemidirectProduct.inr A)).left

omit [Finite F] in
/-- A quotient-trivial actor's Levi displacement satisfies its nonabelian
one-cocycle equation in the full radical. -/
theorem leviDeviation_mul (a : MulAut (PlaneSemidirect J))
    (ha : ∀ p, (a p).right = p.right) (A B : SpecialLinearGroup (Fin 2) F) :
    leviDeviation J a (A * B) =
      leviDeviation J a A * Parameters.planeAction A (leviDeviation J a B) := by
  change (a (SemidirectProduct.inr (A * B))).left = _
  rw [map_mul,map_mul,SemidirectProduct.mul_left,ha]
  rfl

/-- The exact full-residual formula retains both the radical action and
movement of the Levi complement. -/
theorem residualActor_formula (a : MulAut (PlaneSemidirect J))
    (ha : ∀ p, (a p).right = p.right) (p : PlaneSemidirect J) :
    a p = ⟨radicalAction J a p.left * leviDeviation J a p.right,p.right⟩ := by
  have he : a p = a (SemidirectProduct.inl p.left) * a (SemidirectProduct.inr p.right) := by
    rw [←map_mul,SemidirectProduct.inl_left_mul_inr_right]
  rw [he,←radicalAction_inl]
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left,SemidirectProduct.left_inl,
      SemidirectProduct.right_inl,map_one,MulAut.one_apply]
    rfl
  · simp only [SemidirectProduct.mul_right,SemidirectProduct.right_inl,one_mul,ha,
      SemidirectProduct.right_inr]

/-- Compatibility of the two unknowns on the entire radical, with the
literal Levi action and the actual displacement cocycle. -/
theorem radicalAction_compatibility (a : MulAut (PlaneSemidirect J))
    (ha : ∀ p, (a p).right = p.right) (A : SpecialLinearGroup (Fin 2) F) (u : Parameters J) :
    radicalAction J a (Parameters.planeAction A u) =
      leviDeviation J a A * Parameters.planeAction A (radicalAction J a u) *
        (leviDeviation J a A)⁻¹ := by
  apply SemidirectProduct.inl_injective (φ := Parameters.planeAction (J := J))
  rw [radicalAction_inl,SemidirectProduct.inl_aut,map_mul,map_mul,map_inv]
  rw [←radicalAction_inl]
  have he : a (SemidirectProduct.inr A) =
      SemidirectProduct.inl (leviDeviation J a A) * SemidirectProduct.inr A := by
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left,SemidirectProduct.left_inl,
        SemidirectProduct.right_inl,map_one,SemidirectProduct.left_inr,mul_one]
      rfl
    · simpa using ha (SemidirectProduct.inr A)
  simp only [map_inv,he,map_mul,map_inv]
  rw [SemidirectProduct.inl_aut]
  simp only [map_inv]
  group
end Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
