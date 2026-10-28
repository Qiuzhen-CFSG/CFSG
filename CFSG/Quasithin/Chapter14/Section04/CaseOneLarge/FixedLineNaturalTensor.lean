module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineProjective
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Coordinates
public import Theory.Representation.BinaryPermutation.ThreeTensor
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FieldDescent

/-!
# The natural tensor action from the coefficient transposition centralizer

The surviving five-point coefficient image is the centralizer of a
transposition. Its central involution acts nontrivially on the scalar field.
Finite-field descent conjugates that involution to Frobenius, whose literal
semilinear centralizer is GL₂(2) × Aut(F₄). Conjugating the coefficient basis
therefore splits the original action into a binary two-plane and the natural
semilinear four-space.

The resulting whole-group isomorphism and linear coordinate map intertwine
the original action with S₃ × S₅ on the natural tensor. The three-point factor
uses its actual augmentation-core representation, and the alternating
five-point factor is explicitly identified with the natural SL₂(4) action.
Private helpers retain the coefficient and component maps throughout.

Source: Aschbacher--Smith, G.11.8 and 14.4.2(5), printed pp.368--369,1006;
refs/quasithin.pdf. The original-flag application is in FixedLineNaturalSource.
-/

public noncomputable section
open Subgroup Module Representation Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineDescent
open FixedLineSemilinear
private local instance descentCanonicalAlgebra : Algebra (ZMod 2) Field := ZMod.algebra _ 2
private abbrev F := SL2FourNatural.F
private abbrev Gamma4 := SL2FourNatural.SemilinearNormalizer.Gamma
private abbrev GL4 := SL2FourNatural.SemilinearNormalizer.LinearGroup
private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)
private abbrev Aut4 := F ≃+* F
private instance finiteAut4 : Finite Aut4 := Nat.finite_of_card_ne_zero (by
  rw [SL2FourNatural.SemilinearNormalizer.automorphism_card]
  decide)

private def fieldTransport : (Field ≃+* Field) ≃* Aut4 where
  toFun σ := (SL2FourNatural.fieldEquiv.trans σ).trans SL2FourNatural.fieldEquiv.symm
  invFun σ := (SL2FourNatural.fieldEquiv.symm.trans σ).trans SL2FourNatural.fieldEquiv
  left_inv σ := by apply RingEquiv.ext; intro x; simp
  right_inv σ := by apply RingEquiv.ext; intro x; simp
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    change SL2FourNatural.fieldEquiv.symm (σ (τ (SL2FourNatural.fieldEquiv x))) =
      SL2FourNatural.fieldEquiv.symm (σ (SL2FourNatural.fieldEquiv
        (SL2FourNatural.fieldEquiv.symm (τ (SL2FourNatural.fieldEquiv x)))))
    rw [SL2FourNatural.fieldEquiv.apply_symm_apply]

private instance finiteCanonicalAut : Finite (Field ≃+* Field) :=
  Finite.of_equiv Aut4 fieldTransport.toEquiv.symm

private def gammaTransport : Gamma ≃* Gamma4 :=
  SemidirectProduct.congr
    (Matrix.GeneralLinearGroup.coefficientEquiv SL2FourNatural.fieldEquiv.symm)
    fieldTransport (by
      intro σ
      apply MulEquiv.ext
      intro A
      apply Units.ext
      funext i j
      change SL2FourNatural.fieldEquiv.symm (σ (A.val i j)) =
        SL2FourNatural.fieldEquiv.symm (σ (SL2FourNatural.fieldEquiv
          (SL2FourNatural.fieldEquiv.symm (A.val i j))))
      rw [SL2FourNatural.fieldEquiv.apply_symm_apply])

private instance finiteGamma4 : Finite Gamma4 := Nat.finite_of_card_ne_zero (by
  rw [SL2FourNatural.SemilinearNormalizer.gamma_card]
  decide)

private instance finiteGamma : Finite Gamma :=
  Finite.of_equiv Gamma4 gammaTransport.toEquiv.symm

private def binaryMatrix : GL2 →* GL4 :=
  Matrix.GeneralLinearGroup.map (algebraMap (ZMod 2) F)

private theorem binaryMatrix_injective : Function.Injective binaryMatrix := by
  intro A B h
  apply Units.ext
  ext i j
  apply (algebraMap (ZMod 2) F).injective
  exact congrArg (fun M : GL4 => M.val i j) h

private theorem binaryMatrix_fixed (σ : Aut4) (A : GL2) :
    Matrix.GeneralLinearGroup.coefficientAction F σ (binaryMatrix A) = binaryMatrix A := by
  apply Units.ext
  funext i j
  change σ (algebraMap (ZMod 2) F (A.val i j)) = algebraMap (ZMod 2) F (A.val i j)
  generalize A.val i j = x
  fin_cases x
  · change σ (algebraMap (ZMod 2) F 0) = algebraMap (ZMod 2) F 0
    rw [map_zero,map_zero]
  · change σ (algebraMap (ZMod 2) F 1) = algebraMap (ZMod 2) F 1
    rw [map_one,map_one]

private def binaryField : GL2 × Aut4 →* Gamma4 where
  toFun z := ⟨binaryMatrix z.1,z.2⟩
  map_one' := by
    apply SemidirectProduct.ext
    · exact binaryMatrix.map_one
    · rfl
  map_mul' z w := by
    apply SemidirectProduct.ext
    swap
    · rfl
    change binaryMatrix (z.1*w.1) = binaryMatrix z.1 *
      Matrix.GeneralLinearGroup.coefficientAction F z.2 (binaryMatrix w.1)
    rw [map_mul,binaryMatrix_fixed]

private theorem binaryField_injective : Function.Injective binaryField := by
  intro z w h
  exact Prod.ext (binaryMatrix_injective (congrArg SemidirectProduct.left h))
    (congrArg SemidirectProduct.right h)

private theorem binaryMatrix_range (A : GL4)
    (hA : Matrix.GeneralLinearGroup.coefficientAction F SL2FourNatural.fieldFrobenius A = A) :
    A ∈ binaryMatrix.range := by
  have he (i j : Fin 2) : ∃ c : ZMod 2, algebraMap (ZMod 2) F c = A.val i j := by
    have h := congrArg (fun M : GL4 => M.val i j) hA
    rcases (SL2FourNatural.fieldFrobenius_fixed (A.val i j)).mp h with h | h
    · exact ⟨0,by simpa using h.symm⟩
    · exact ⟨1,by simpa using h.symm⟩
  choose M hM using he
  have hm : Matrix.map M (algebraMap (ZMod 2) F) = A.val := by funext i j; exact hM i j
  have hd : Matrix.det M ≠ 0 := by
    intro hz
    have hh : (algebraMap (ZMod 2) F) (Matrix.det M) = Matrix.det A.val :=
      ((algebraMap (ZMod 2) F).map_det M).trans
        (congrArg Matrix.det ((RingHom.mapMatrix_apply (algebraMap (ZMod 2) F) M).trans hm))
    rw [hz,map_zero] at hh
    exact Matrix.GeneralLinearGroup.det_ne_zero A hh.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hd,?_⟩
  apply Units.ext
  exact hm

private theorem centralizer_fieldElement :
    centralizer ({SL2FourNatural.SemilinearNormalizer.fieldElement} : Set Gamma4) =
      binaryField.range := by
  ext z
  constructor
  · intro hz
    have hh := congrArg SemidirectProduct.left (mem_centralizer_singleton_iff.mp hz)
    have hm : Matrix.GeneralLinearGroup.coefficientAction F SL2FourNatural.fieldFrobenius z.left =
        z.left := by
      simpa [SL2FourNatural.SemilinearNormalizer.fieldElement] using hh.symm
    obtain ⟨A,hA⟩ := binaryMatrix_range z.left hm
    exact ⟨(A,z.right),SemidirectProduct.ext hA rfl⟩
  · rintro ⟨⟨A,σ⟩,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply SemidirectProduct.ext
    · change binaryMatrix A * Matrix.GeneralLinearGroup.coefficientAction F σ 1 =
        1 * Matrix.GeneralLinearGroup.coefficientAction F SL2FourNatural.fieldFrobenius (binaryMatrix A)
      rw [map_one,mul_one,one_mul,binaryMatrix_fixed]
    · change σ * SL2FourNatural.fieldFrobenius = SL2FourNatural.fieldFrobenius * σ
      rcases SL2FourNatural.SemilinearNormalizer.fieldAutomorphism_cases σ with rfl | rfl
      · simp
      · rfl

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineDescent

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
open FixedLineDescent
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {H : Subgroup D} (a : Coordinates ρ H)

private theorem coefficient_central_field_involution
    (t : Equiv.Perm (Fin 5)) (ht : t.IsSwap)
    (e : a.coefficient.range ≃* centralizer ({t} : Set (Equiv.Perm (Fin 5))))
    (he : ∀ b, (e b).val = a.coefficientFive b) :
    ∃ z : a.coefficient.range, z ^ 2 = 1 ∧ a.coefficientField z ≠ 1 ∧
      ∀ b : a.coefficient.range, b*z=z*b := by
  let t' : centralizer ({t} : Set (Equiv.Perm (Fin 5))) :=
    ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩
  let z := e.symm t'
  have hz : a.coefficientFive z = t := (he z).symm.trans
    (congrArg Subtype.val (e.apply_symm_apply t'))
  refine ⟨z,?_,?_,?_⟩
  · apply e.injective
    rw [map_pow,map_one,e.apply_symm_apply]
    apply Subtype.ext
    exact ht.orderOf ▸ pow_orderOf_eq_one t
  · intro hh
    have hh' := Equiv.Perm.mem_alternatingGroup.mp ((a.coefficientFive_even_iff z).mpr hh)
    rw [hz,ht.sign_eq] at hh'
    exact (by decide : (-1 : ℤˣ) ≠ 1) hh'
  · intro b
    apply e.injective
    rw [map_mul,map_mul,e.apply_symm_apply]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (e b).property

/-- The actual coefficient action admits a basis in which its matrices are
binary and its field factor is independent. The equivalence retains the
conjugated semilinear matrices, not merely their abstract group type. -/
private theorem coefficient_binary_descent
    (t : Equiv.Perm (Fin 5)) (ht : t.IsSwap)
    (e : a.coefficient.range ≃* centralizer ({t} : Set (Equiv.Perm (Fin 5))))
    (he : ∀ b, (e b).val = a.coefficientFive b) :
    ∃ P : GL4, ∃ f : a.coefficient.range ≃* GL2 × Aut4,
      ∀ b, gammaTransport b.val =
        SemidirectProduct.inl P * binaryField (f b) * (SemidirectProduct.inl P)⁻¹ := by
  obtain ⟨z,hz2,hzf,hzc⟩ := a.coefficient_central_field_involution t ht e he
  have hright : (gammaTransport z.val).right = SL2FourNatural.fieldFrobenius := by
    rcases SL2FourNatural.SemilinearNormalizer.fieldAutomorphism_cases
      (gammaTransport z.val).right with hh | hh
    · apply False.elim
      apply hzf
      apply fieldTransport.injective
      rw [a.coefficientField_apply]
      exact hh.trans fieldTransport.map_one.symm
    · exact hh
  have hpow : (gammaTransport z.val)^2=1 := by
    rw [←map_pow]
    have hh : z.val^2=1 := congrArg Subtype.val hz2
    rw [hh,map_one]
  obtain ⟨P,hP⟩ := SL2FourNatural.SemilinearNormalizer.field_involution_conjugate
    (gammaTransport z.val) hright hpow
  let c := MulAut.conj (SemidirectProduct.inl P : Gamma4)⁻¹
  let j : a.coefficient.range →* Gamma4 :=
    c.toMonoidHom.comp (gammaTransport.toMonoidHom.comp a.coefficient.range.subtype)
  have hj : Function.Injective j := c.injective.comp (gammaTransport.injective.comp Subtype.val_injective)
  have hjz : j z = SL2FourNatural.SemilinearNormalizer.fieldElement := by
    change (SemidirectProduct.inl P)⁻¹ * gammaTransport z.val *
      ((SemidirectProduct.inl P)⁻¹)⁻¹ = _
    rw [hP]
    group
  have hle : j.range ≤ binaryField.range := by
    rw [←centralizer_fieldElement]
    rintro _ ⟨b,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←hjz,←map_mul,←map_mul,hzc]
  have hcard : Nat.card a.coefficient.range = 12 := by
    rw [Nat.card_congr e.toEquiv,Equiv.Perm.nat_card_centralizer,
      Equiv.Perm.isSwap_iff_cycleType.mp ht]
    norm_num [Nat.factorial]
  have hbinary : Nat.card (GL2 × Aut4) = 12 := by
    rw [Nat.card_prod,Matrix.card_GL_field,
      SL2FourNatural.SemilinearNormalizer.automorphism_card]
    norm_num [Fintype.card_fin, ZMod.card, Fin.prod_univ_two]
  have hrange : j.range = binaryField.range := eq_of_le_of_card_ge hle (by
    rw [←Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,
      ←Nat.card_congr (MonoidHom.ofInjective binaryField_injective).toEquiv,hcard,hbinary])
  let f := (MonoidHom.ofInjective hj).trans ((MulEquiv.subgroupCongr hrange).trans
    (MonoidHom.ofInjective binaryField_injective).symm)
  refine ⟨P,f,?_⟩
  intro b
  have hf : binaryField (f b) = j b := by
    exact congrArg Subtype.val ((MonoidHom.ofInjective binaryField_injective).apply_symm_apply
      ((MulEquiv.subgroupCongr hrange) ((MonoidHom.ofInjective hj) b)))
  rw [hf]
  change gammaTransport b.val = _ * ((SemidirectProduct.inl P)⁻¹ * gammaTransport b.val *
    ((SemidirectProduct.inl P)⁻¹)⁻¹) * _
  group

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineDescent
open Representation.SL2AutomorphismNatural FixedLineSemilinear

private abbrev Params4 := Parameters (F := F)
private abbrev Blocks := Fin 2 → SL2FourNatural.V

private def parameterGamma : Params4 →* Gamma4 :=
  SemidirectProduct.map Matrix.SpecialLinearGroup.toGL (MonoidHom.id _) (by
    intro σ
    apply MonoidHom.ext
    intro g
    apply Units.ext
    rfl)

private instance finiteParams4 : Finite Params4 :=
  Finite.of_equiv (SL2FourNatural.SL × Aut4) SemidirectProduct.equivProd.symm

private def natural4 : Params4 →* (SL2FourNatural.V ≃ₗ[ZMod 2] SL2FourNatural.V) :=
  SL2FourNatural.SemilinearNormalizer.natural.comp parameterGamma

private theorem natural4_apply (g : Params4) (v : SL2FourNatural.V) :
    natural4 g v = g.left.val.mulVec (fun i => g.right (v i)) := rfl

private theorem natural4_semilinear (g : Params4) (c : F) (v : SL2FourNatural.V) :
    natural4 g (c • v) = g.right c • natural4 g v :=
  SL2FourNatural.SemilinearNormalizer.natural_smul (parameterGamma g) c v

private def parameterTransport : Parameters (F := Field) ≃* Params4 :=
  SemidirectProduct.congr SL2FourNatural.standardGroupEquiv.symm fieldTransport (by
    intro σ
    apply MulEquiv.ext
    intro A
    apply Subtype.ext
    funext i j
    change SL2FourNatural.fieldEquiv.symm (σ (A.val i j)) =
      SL2FourNatural.fieldEquiv.symm (σ (SL2FourNatural.fieldEquiv
        (SL2FourNatural.fieldEquiv.symm (A.val i j))))
    rw [SL2FourNatural.fieldEquiv.apply_symm_apply])

private local instance blockCanonicalAlgebra : Algebra (ZMod 2) Field := ZMod.algebra _ 2

private def fieldSpace : (Fin 2 → Plane) ≃ₗ[ZMod 2] Blocks where
  toFun v i j := SL2FourNatural.fieldEquiv.symm (v i j)
  invFun v i j := SL2FourNatural.fieldEquiv (v i j)
  left_inv v := by funext i j; exact SL2FourNatural.fieldEquiv.apply_symm_apply _
  right_inv v := by funext i j; exact SL2FourNatural.fieldEquiv.symm_apply_apply _
  map_add' v w := by funext i j; exact map_add SL2FourNatural.fieldEquiv.symm _ _
  map_smul' c v := by
    funext i j
    change SL2FourNatural.fieldEquiv.symm (c • v i j) = c • SL2FourNatural.fieldEquiv.symm (v i j)
    exact ZMod.map_smul SL2FourNatural.fieldEquiv.symm.toAddMonoidHom c (v i j)

private def row (P : GL4) : Blocks ≃ₗ[ZMod 2] Blocks :=
  (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) (ZMod 2) F).trans
    ((LinearEquiv.piCongrRight (fun _ => SL2FourNatural.SemilinearNormalizer.linear P)).trans
      (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) (ZMod 2) F))

private theorem row_apply (P : GL4) (z : Blocks) (i k : Fin 2) :
    row P z i k = ∑ j : Fin 2, P.val i j * z j k := rfl

private theorem row_mul (P Q : GL4) (z : Blocks) : row (P*Q) z = row P (row Q z) := by
  funext i k
  exact congrFun (Matrix.mulVec_mulVec (fun j => z j k) P.val Q.val).symm i

private theorem row_one (z : Blocks) : row 1 z = z := by
  funext i k
  exact congrFun (Matrix.one_mulVec (fun j => z j k)) i

private def diagonal (g : Params4) : Blocks ≃ₗ[ZMod 2] Blocks :=
  LinearEquiv.piCongrRight (fun _ => natural4 g)

private theorem diagonal_row (g : Params4) (P : GL4) (z : Blocks) :
    diagonal g (row P z) = row (Matrix.GeneralLinearGroup.coefficientAction F g.right P)
      (diagonal g z) := by
  funext i
  have hr : row P z i = ∑ j : Fin 2, P.val i j • z j := by
    funext k
    simp only [row_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change natural4 g (row P z i) = _
  rw [hr,map_sum]
  simp only [natural4_semilinear]
  rfl

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineDescent

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
open FixedLineDescent Representation.SL2AutomorphismNatural
private local instance naturalTensorCanonicalAlgebra : Algebra (ZMod 2) Field := ZMod.algebra _ 2
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {H : Subgroup D} (a : Coordinates ρ H)

private def naturalParameters : D →* Params4 :=
  parameterTransport.toMonoidHom.comp (parameterEquiv.symm.toMonoidHom.comp a.automorphism)

private theorem naturalParameters_field (g : D) :
    (a.naturalParameters g).right = (gammaTransport (a.coefficient g)).right := by
  apply congrArg fieldTransport
  exact (a.same_field g).symm

private theorem fieldSpace_action (g : D) (w : W) :
    fieldSpace (a.space (ρ g w)) = row (gammaTransport (a.coefficient g)).left
      (diagonal (a.naturalParameters g) (fieldSpace (a.space w))) := by
  funext i k
  have hh := congrArg SL2FourNatural.fieldEquiv.symm (congrFun (a.equivariant g w i) k)
  change SL2FourNatural.fieldEquiv.symm (a.space (ρ g w) i k) = _
  rw [hh,FixedLineDescent.row_apply]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change SL2FourNatural.fieldEquiv.symm
    ((parameterEquiv.symm (a.automorphism g)).left.val.mulVec
      (fun l => (parameterEquiv.symm (a.automorphism g)).right (a.space w j l)) k) =
    natural4 (a.naturalParameters g) (fieldSpace (a.space w) j) k
  rw [natural4_apply]
  simp only [Matrix.mulVec,dotProduct,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro l _
  change _ = SL2FourNatural.fieldEquiv.symm
    ((parameterEquiv.symm (a.automorphism g)).left.val k l) *
      SL2FourNatural.fieldEquiv.symm
        ((parameterEquiv.symm (a.automorphism g)).right
          (SL2FourNatural.fieldEquiv (SL2FourNatural.fieldEquiv.symm (a.space w j l))))
  rw [SL2FourNatural.fieldEquiv.apply_symm_apply]

private theorem descended_field (P : GL4)
    (f : a.coefficient.range ≃* GL2 × Aut4)
    (hf : ∀ b, gammaTransport b.val =
      SemidirectProduct.inl P * binaryField (f b) * (SemidirectProduct.inl P)⁻¹)
    (g : D) : (f (a.coefficient.rangeRestrict g)).2 = (a.naturalParameters g).right := by
  rw [a.naturalParameters_field]
  have hh := congrArg SemidirectProduct.right (hf (a.coefficient.rangeRestrict g))
  simpa only [SemidirectProduct.mul_right,SemidirectProduct.inv_right,
    SemidirectProduct.right_inl,inv_one,one_mul,mul_one,binaryField,MonoidHom.coe_mk,OneHom.coe_mk,MonoidHom.coe_rangeRestrict] using hh.symm

private def descendedActor (f : a.coefficient.range ≃* GL2 × Aut4) : D →* GL2 × Params4 :=
  ((MonoidHom.fst GL2 Aut4).comp (f.toMonoidHom.comp a.coefficient.rangeRestrict)).prod
    a.naturalParameters

private theorem descendedActor_injective (P : GL4)
    (f : a.coefficient.range ≃* GL2 × Aut4)
    (hf : ∀ b, gammaTransport b.val =
      SemidirectProduct.inl P * binaryField (f b) * (SemidirectProduct.inl P)⁻¹) :
    Function.Injective (a.descendedActor f) := by
  intro g h he
  have hp : a.naturalParameters g = a.naturalParameters h := congrArg Prod.snd he
  have hc : a.coefficient g = a.coefficient h := by
    suffices hh : a.coefficient.rangeRestrict g = a.coefficient.rangeRestrict h from
      congrArg Subtype.val hh
    apply f.injective
    apply Prod.ext
    · exact congrArg (fun z : GL2 × Params4 => z.1) he
    · rw [a.descended_field P f hf,a.descended_field P f hf,hp]
  apply a.faithful
  apply Prod.ext ?_ hc
  apply parameterEquiv.symm.injective
  exact parameterTransport.injective hp

private theorem descendedActor_surjective (P : GL4)
    (f : a.coefficient.range ≃* GL2 × Aut4)
    (hf : ∀ b, gammaTransport b.val =
      SemidirectProduct.inl P * binaryField (f b) * (SemidirectProduct.inl P)⁻¹) :
    Function.Surjective (a.descendedActor f) := by
  let : Finite a.SplitGroup := Finite.of_equiv
    (SL(2,Field) × a.coefficient.range) SemidirectProduct.equivProd.symm
  let : Finite D := Finite.of_injective a.splitEquiv a.splitEquiv.injective
  have hc : Nat.card D = Nat.card (GL2 × Params4) := by
    rw [Nat.card_congr a.splitEquiv.toEquiv,SemidirectProduct.card,Nat.card_congr f.toEquiv]
    simp only [Nat.card_prod,SemidirectProduct.card]
    rw [←Nat.card_congr SL2FourNatural.standardGroupEquiv.toEquiv]
    ring
  exact ((Nat.bijective_iff_injective_and_card (a.descendedActor f)).mpr
    ⟨a.descendedActor_injective P f hf,hc⟩).surjective

/-- The descended coordinates recognize the whole original group and action
as a binary two-plane tensored with the natural semilinear four-space. -/
private theorem natural_tensor_block_coordinates
    (t : Equiv.Perm (Fin 5)) (ht : t.IsSwap)
    (e : a.coefficient.range ≃* centralizer ({t} : Set (Equiv.Perm (Fin 5))))
    (he : ∀ b, (e b).val = a.coefficientFive b) :
    ∃ actor : D ≃* GL2 × Params4, ∃ space : W ≃ₗ[ZMod 2] Blocks,
      (∀ g, (actor g).2 = a.naturalParameters g) ∧
      ∀ g w i, space (ρ g w) i = ∑ j : Fin 2,
        (algebraMap (ZMod 2) F ((actor g).1.val i j)) •
          natural4 (actor g).2 (space w j) := by
  obtain ⟨P,f,hf⟩ := a.coefficient_binary_descent t ht e he
  let actor := MulEquiv.ofBijective (a.descendedActor f)
    ⟨a.descendedActor_injective P f hf,a.descendedActor_surjective P f hf⟩
  let space := (a.space.trans fieldSpace).trans (row P⁻¹)
  refine ⟨actor,space,fun _ => rfl,?_⟩
  intro g w
  have hcoeff : P⁻¹ * (gammaTransport (a.coefficient g)).left =
      binaryMatrix (f (a.coefficient.rangeRestrict g)).1 *
        Matrix.GeneralLinearGroup.coefficientAction F (a.naturalParameters g).right P⁻¹ := by
    have hh := congrArg SemidirectProduct.left (hf (a.coefficient.rangeRestrict g))
    have hfield := a.descended_field P f hf g
    change (gammaTransport (a.coefficient g)).left =
      P * binaryMatrix (f (a.coefficient.rangeRestrict g)).1 *
        Matrix.GeneralLinearGroup.coefficientAction F (f (a.coefficient.rangeRestrict g)).2 P⁻¹ at hh
    rw [hh,hfield]
    group
  have haction : space (ρ g w) = row (binaryMatrix (f (a.coefficient.rangeRestrict g)).1)
      (diagonal (a.naturalParameters g) (space w)) := by
    change row P⁻¹ (fieldSpace (a.space (ρ g w))) = _
    rw [a.fieldSpace_action,←row_mul,hcoeff,row_mul]
    rw [←diagonal_row]
    rfl
  intro i
  rw [haction]
  funext k
  rfl

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineDescent
open Representation.SL2AutomorphismNatural
open scoped TensorProduct
private abbrev Three := Equiv.Perm (Fin 3)
private abbrev Five := Equiv.Perm (Fin 5)
private abbrev Alt := alternatingGroup (Fin 5)
private abbrev BinaryPlane := Fin 2 → ZMod 2

private def corePlane : BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] BinaryPlane where
  toFun n := ![n.val 0,n.val 1]
  invFun v := ⟨![v 0,v 1,-v 0-v 1],by
    rw [BinaryPermutation.mem_core,Fin.sum_univ_three]
    change v 0 + v 1 + (-v 0-v 1) = 0
    ring⟩
  left_inv n := by
    apply Subtype.ext
    have hn := n.property
    rw [BinaryPermutation.mem_core,Fin.sum_univ_three] at hn
    ext i
    fin_cases i
    · rfl
    · rfl
    · change -n.val 0-n.val 1 = n.val 2
      linear_combination -hn
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

private def planeGL : GL2 ≃* (BinaryPlane ≃ₗ[ZMod 2] BinaryPlane) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryPlane)

private theorem planeGL_apply (A : GL2) (v : BinaryPlane) : planeGL A v = A.val.mulVec v :=
  Matrix.GeneralLinearGroup.toLin_apply A v

private def threeMatrix : Three →* GL2 where
  toFun s := planeGL.symm (corePlane.symm.trans
    ((LinearEquiv.ofBijective (BinaryPermutation.coreRepresentation (Fin 3) s)
      ((BinaryPermutation.coreRepresentation (Fin 3)).apply_bijective s)).trans corePlane))
  map_one' := by
    apply planeGL.injective
    rw [planeGL.apply_symm_apply,planeGL.map_one]
    apply LinearEquiv.ext
    intro v
    change corePlane (BinaryPermutation.coreRepresentation (Fin 3) 1 (corePlane.symm v)) = v
    simp
  map_mul' s t := by
    apply planeGL.injective
    rw [planeGL.apply_symm_apply,planeGL.map_mul,planeGL.apply_symm_apply,planeGL.apply_symm_apply]
    apply LinearEquiv.ext
    intro v
    change corePlane (BinaryPermutation.coreRepresentation (Fin 3) (s*t) (corePlane.symm v)) =
      corePlane (BinaryPermutation.coreRepresentation (Fin 3) s
        (corePlane.symm (corePlane (BinaryPermutation.coreRepresentation (Fin 3) t (corePlane.symm v)))))
    rw [corePlane.symm_apply_apply,map_mul]
    rfl

private theorem threeMatrix_action (s : Three) (v : BinaryPermutation.core (Fin 3)) :
    (threeMatrix s).val.mulVec (corePlane v) = corePlane (BinaryPermutation.coreRepresentation (Fin 3) s v) := by
  have hh := LinearEquiv.congr_fun (planeGL.apply_symm_apply
    (corePlane.symm.trans ((LinearEquiv.ofBijective (BinaryPermutation.coreRepresentation (Fin 3) s)
      ((BinaryPermutation.coreRepresentation (Fin 3)).apply_bijective s)).trans corePlane))) (corePlane v)
  rw [planeGL_apply] at hh
  simpa only [LinearEquiv.trans_apply,corePlane.symm_apply_apply,LinearEquiv.ofBijective_apply,threeMatrix,MonoidHom.coe_mk,OneHom.coe_mk] using hh

private theorem threeMatrix_injective : Function.Injective threeMatrix := by
  have hf : ∀ s t : Three,
      (∀ v : Fin 3 → ZMod 2, (∑ i, v i) = 0 → ∀ i, v (s.symm i) = v (t.symm i)) → s=t := by
    decide +kernel
  intro s t he
  apply hf s t
  intro v hv i
  let n : BinaryPermutation.core (Fin 3) := ⟨v,hv⟩
  have hh := (threeMatrix_action s n).symm.trans ((congrArg
    (fun A : GL2 => A.val.mulVec (corePlane n)) he).trans (threeMatrix_action t n))
  exact congrArg (fun x : BinaryPermutation.core (Fin 3) => x.val i) (corePlane.injective hh)

private def threeEquiv : Three ≃* GL2 := MulEquiv.ofBijective threeMatrix
  ((Nat.bijective_iff_injective_and_card threeMatrix).mpr ⟨threeMatrix_injective,by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    rw [Matrix.card_GL_field]
    norm_num [Nat.factorial,Fin.prod_univ_two]⟩)

private def tensorBlocks :
    (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] SL2FourNatural.V) ≃ₗ[ZMod 2] Blocks :=
  (TensorProduct.comm (ZMod 2) _ _).trans
    (BinaryPermutation.ThreeTensor.pairEquiv.trans (LinearEquiv.finTwoArrow (ZMod 2) _).symm)

private theorem tensorBlocks_tmul (n : BinaryPermutation.core (Fin 3)) (v : SL2FourNatural.V)
    (i : Fin 2) : tensorBlocks (n ⊗ₜ[ZMod 2] v) i = corePlane n i • v := by
  simp only [tensorBlocks,LinearEquiv.trans_apply,TensorProduct.comm_tmul,
    BinaryPermutation.ThreeTensor.pairEquiv_tmul]
  fin_cases i <;> rfl

private def specialAlternating : SL2FourNatural.SL ≃* Alt :=
  (Theory.PSL2.sl2QuotientEquiv F).trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (by rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field])).some

private def automorphismFive : Five ≃* MulAut Alt :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))

private def naturalFive : Params4 ≃* Five :=
  parameterEquiv.trans ((MulAut.congr specialAlternating).trans automorphismFive.symm)

private theorem naturalFive_inner (g : SL2FourNatural.SL) :
    naturalFive (SemidirectProduct.inl g) = (specialAlternating g).val := by
  apply automorphismFive.injective
  change automorphismFive (automorphismFive.symm ((MulAut.congr specialAlternating)
    (parameterEquiv (SemidirectProduct.inl g)))) = _
  rw [automorphismFive.apply_symm_apply]
  have hh : parameterEquiv (SemidirectProduct.inl g) = MulAut.conj g := by
    change parameterAut (SemidirectProduct.inl g) = MulAut.conj g
    exact SemidirectProduct.lift_inl _ _ _ _
  rw [hh]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (specialAlternating (g * specialAlternating.symm x * g⁻¹)).val =
    (specialAlternating g).val * x * (specialAlternating g).val⁻¹
  simp

private def fiveRepresentation : Representation (ZMod 2) (⊤ : Subgroup Five) SL2FourNatural.V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (natural4.comp (naturalFive.symm.toMonoidHom.comp (⊤ : Subgroup Five).subtype))

private theorem fiveRepresentation_natural : LargerDimension.Tensor.IsNaturalFour
    (show Alt ≤ (⊤ : Subgroup Five) from le_top) fiveRepresentation := by
  refine ⟨specialAlternating.symm,LinearEquiv.refl _ _,?_⟩
  intro a v
  have hh : naturalFive.symm a.val = SemidirectProduct.inl (specialAlternating.symm a) := by
    apply naturalFive.injective
    rw [naturalFive.apply_symm_apply,naturalFive_inner,specialAlternating.apply_symm_apply]
  change natural4 (naturalFive.symm a.val) v = SL2FourNatural.action (specialAlternating.symm a) v
  rw [hh]
  rfl

private theorem tensorBlocks_action (s : Three) (p : Params4)
    (z : BinaryPermutation.core (Fin 3) ⊗[ZMod 2] SL2FourNatural.V) (i : Fin 2) :
    tensorBlocks (LargerDimension.Tensor.sourceTensorAction fiveRepresentation
      (s,⟨naturalFive p,mem_top _⟩) z) i = ∑ j : Fin 2,
        (algebraMap (ZMod 2) F ((threeMatrix s).val i j)) •
          natural4 p (tensorBlocks z j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,Pi.add_apply,hz,hw,smul_add,Finset.sum_add_distrib]
  | tmul n v =>
    have hh : fiveRepresentation ⟨naturalFive p,mem_top _⟩ v = natural4 p v := by
      change natural4 (naturalFive.symm (naturalFive p)) v = _
      rw [naturalFive.symm_apply_apply]
    change tensorBlocks ((BinaryPermutation.coreRepresentation (Fin 3) s n) ⊗ₜ[ZMod 2]
      fiveRepresentation ⟨naturalFive p,mem_top _⟩ v) i = _
    rw [hh,tensorBlocks_tmul,←threeMatrix_action]
    change (∑ j : Fin 2, (threeMatrix s).val i j * corePlane n j) • natural4 p v = _
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j _
    rw [tensorBlocks_tmul,(natural4 p).map_smul]
    rw [IsScalarTower.algebraMap_smul F]
    exact mul_smul _ _ _

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineDescent

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
open FixedLineDescent LargerDimension.Tensor
open scoped TensorProduct
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {H : Subgroup D} (a : Coordinates ρ H)

/-- The surviving coefficient centralizer gives the exact natural tensor row,
with an actual whole-group isomorphism and the original action intertwined. -/
theorem natural_tensor_coordinates
    (t : Equiv.Perm (Fin 5)) (ht : t.IsSwap)
    (e : a.coefficient.range ≃* centralizer ({t} : Set (Equiv.Perm (Fin 5))))
    (he : ∀ b, (e b).val = a.coefficientFive b) :
    ∃ σ : Representation (ZMod 2) (⊤ : Subgroup (Equiv.Perm (Fin 5))) SL2FourNatural.V,
      IsNaturalFour le_top σ ∧
      ∃ actor : D ≃* Equiv.Perm (Fin 3) × (⊤ : Subgroup (Equiv.Perm (Fin 5))),
      ∃ space : W ≃ₗ[ZMod 2] (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] SL2FourNatural.V),
        ∀ g w, space (ρ g w) = sourceTensorAction σ (actor g) (space w) := by
  obtain ⟨b,s,hb,hs⟩ := a.natural_tensor_block_coordinates t ht e he
  let actor := b.trans (MulEquiv.prodCongr threeEquiv.symm (naturalFive.trans Subgroup.topEquiv.symm))
  let space := s.trans tensorBlocks.symm
  refine ⟨fiveRepresentation,fiveRepresentation_natural,actor,space,?_⟩
  intro g w
  apply tensorBlocks.injective
  change tensorBlocks (tensorBlocks.symm (s (ρ g w))) = _
  rw [tensorBlocks.apply_symm_apply]
  have hactor : actor g = (threeEquiv.symm (b g).1,
      ⟨naturalFive (b g).2,mem_top _⟩) := rfl
  rw [hactor]
  funext i
  rw [hs,tensorBlocks_action]
  have hm : threeMatrix (threeEquiv.symm (b g).1) = (b g).1 := threeEquiv.apply_symm_apply _
  rw [hm]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  exact (congrFun (tensorBlocks.apply_symm_apply (s w)) j).symm

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
