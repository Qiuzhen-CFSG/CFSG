module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortQuotient
public import Theory.GroupTheory.ConjugacyOrderCensus
public import Mathlib.GroupTheory.Sylow

/-!
# Long-root lifts through the full unitary short-root line

In the residual short-root centralizer, the long-root conjugacy class is
parametrized by the nonzero pairs (r,s) over the fixed field: its symmetric
Hermitian matrix is [[r²,rs],[rs,s²]]. Completing a nonzero column to SL₂
proves surjectivity, while injectivity of Frobenius proves uniqueness.
Consequently this class has q²−1 elements, and its centralizer contains a
Sylow two-subgroup of the residual short-root centralizer.

The two diagonal entries survive quotienting by the entire short-root
line. Thus this quotient is injective on the long-root class, and the
already proved quotient transitivity gives a unique long-root lift of
every nonzero orthogonal quotient vector. The Chapter6 application uses
the same original short and long roots and the literal ambient quotient.

Source: Aschbacher–Smith F.4.42, printed pp.295–296 of
`refs/quasithin.pdf`. These local orbit and lifting results do not establish
the ambient unique-fixed-coset or outer-transfer assertions.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
local notation "C" => shortCentralizer F σ hσ

private def rootPair (v : K × K) : C :=
  radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd
    (symmetric F σ (v.1^2) (v.1*v.2) (v.2^2)))

private theorem rootPair_injective : Function.Injective (rootPair F σ hσ) := by
  intro v w he
  have hh : symmetric F σ (v.1^2) (v.1*v.2) (v.2^2) =
      symmetric F σ (w.1^2) (w.1*w.2) (w.2^2) := by
    apply Multiplicative.ofAdd.injective
    exact radicalHom_injective F σ hσ (congrArg (fun x : C => x.val) he)
  apply Prod.ext
  · apply (frobeniusEquiv K 2).injective
    apply Subtype.ext
    exact congrArg (fun X : hermitianMatrices F σ => X.val 0 0) hh
  · apply (frobeniusEquiv K 2).injective
    apply Subtype.ext
    exact congrArg (fun X : hermitianMatrices F σ => X.val 1 1) hh

private theorem conjugate_long (a : C) :
    ∃ v : K × K, v ≠ 0 ∧ a * longMark F σ hσ * a⁻¹ = rootPair F σ hσ v := by
  let A := factorRestriction F (form F σ hσ) a.val
  have hA := (mem_fixedSL F σ A).mp ((mem_shortCentralizer F σ hσ a.val).mp a.property)
  let v : K × K := (⟨A.val 0 0,hA 0 0⟩,⟨A.val 1 0,hA 1 0⟩)
  have hv : v ≠ 0 := by
    intro he
    have h0 : A.val 0 0 = 0 := congrArg (fun p : K × K => (p.1 : F)) he
    have h1 : A.val 1 0 = 0 := congrArg (fun p : K × K => (p.2 : F)) he
    have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
      simpa only [det_fin_two] using A.property
    simp only [h0,h1,zero_mul,mul_zero,sub_self] at hd
    exact zero_ne_one hd
  refine ⟨v,hv,?_⟩
  change a * radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd (longParameter F σ)) * a⁻¹ = _
  rw [radicalIntoCentralizer_conj]
  apply congrArg (radicalIntoCentralizer F σ hσ)
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  change A.val * !![1,0;0,0] * adjoint σ A.val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetric,fixedHermitianEquiv,v,adjoint,mul_apply,Fin.sum_univ_two,hA,pow_two,mul_comm]

private theorem rootPair_conjugate (v : K × K) (hv : v ≠ 0) :
    IsConj (longMark F σ hσ) (rootPair F σ hσ v) := by
  have hv' : (![v.1,v.2] : Fin 2 → K) ≠ 0 := by
    intro he
    exact hv (Prod.ext (congrFun he 0) (congrFun he 1))
  obtain ⟨B,hB⟩ := Matrix.SL2.exists_mulVec_eq K ![1,0] ![v.1,v.2]
    (by intro he; exact one_ne_zero (congrFun he 0)) hv'
  have hb0 : B.val 0 0 = v.1 := by
    simpa [mulVec,dotProduct,Fin.sum_univ_two] using congrFun hB 0
  have hb1 : B.val 1 0 = v.2 := by
    simpa [mulVec,dotProduct,Fin.sum_univ_two] using congrFun hB 1
  let A := SpecialLinearGroup.map (FixedBy.subfield F σ).subtype B
  let a := fixedLevi F σ hσ ⟨A,⟨B,rfl⟩⟩
  refine isConj_iff.mpr ⟨a,?_⟩
  change a * radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd (longParameter F σ)) * a⁻¹ = _
  rw [radicalIntoCentralizer_conj]
  simp only [a,fixedLevi,factorRestriction_levi]
  apply congrArg (radicalIntoCentralizer F σ hσ)
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  have ha0 : A.val 0 0 = (v.1 : F) := congrArg Subtype.val hb0
  have ha1 : A.val 1 0 = (v.2 : F) := congrArg Subtype.val hb1
  have hσr : σ (v.1 : F) = v.1 := v.1.property
  have hσs : σ (v.2 : F) = v.2 := v.2.property
  change A.val * !![1,0;0,0] * adjoint σ A.val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetric,fixedHermitianEquiv,adjoint,mul_apply,Fin.sum_univ_two,ha0,ha1,
      hσr,hσs,pow_two,mul_comm]

/-- Nonzero fixed-field pairs parametrize the long-root class in the actual
short-root centralizer, with no quotient or central scalar ambiguity. -/
private def longClassEquiv : {v : K × K // v ≠ 0} ≃ {x : C // IsConj (longMark F σ hσ) x} :=
  Equiv.ofBijective (fun v => ⟨rootPair F σ hσ v.val,rootPair_conjugate F σ hσ v.val v.property⟩) (by
    constructor
    · intro v w he
      exact Subtype.ext (rootPair_injective F σ hσ (congrArg Subtype.val he))
    · rintro ⟨x,hx⟩
      obtain ⟨a,rfl⟩ := isConj_iff.mp hx
      obtain ⟨v,hv,he⟩ := conjugate_long F σ hσ a
      exact ⟨⟨v,hv⟩,Subtype.ext he.symm⟩)

/-- The exact local long-root class size is q²−1. -/
theorem longClass_card :
    Nat.card {x : C // IsConj (longMark F σ hσ) x} = (Nat.card K)^2 - 1 := by
  rw [←Nat.card_congr (longClassEquiv F σ hσ)]
  let := Fintype.ofFinite (K × K)
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [←Nat.card_eq_fintype_card,Nat.card_prod,Nat.card_unique,pow_two]

/-- The long-root centralizer has the same exact odd index. -/
theorem long_centralizer_index :
    (centralizer ({longMark F σ hσ} : Set C)).index = (Nat.card K)^2 - 1 := by
  have he := ConjClasses.nat_card_carrier_mul_card_centralizer (longMark F σ hσ)
  change Nat.card {x : C // IsConj (longMark F σ hσ) x} * _ = _ at he
  rw [longClass_card] at he
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := centralizer ({longMark F σ hσ} : Set C)))
  rw [mul_comm,Subgroup.card_mul_index]
  exact he.symm

/-- A Sylow of the genuine residual short-root centralizer centralizes the
same marked long root. This is local Sylow placement, not ambient transfer. -/
theorem exists_long_centralizing_sylow :
    ∃ P : Sylow 2 C, (P : Subgroup C) ≤ centralizer ({longMark F σ hσ} : Set C) := by
  let Z := centralizer ({longMark F σ hσ} : Set C)
  have hindex : ¬ 2 ∣ Z.index := by
    rw [long_centralizer_index]
    let := Fintype.ofFinite K
    obtain ⟨n,_,hn⟩ := FiniteField.card K 2
    have hn' : Nat.card K = 2^(n : ℕ) := by rwa [Nat.card_eq_fintype_card]
    have hpow : 2 ∣ (Nat.card K)^2 := dvd_pow (by rw [hn']; exact dvd_pow_self 2 n.ne_zero) (by decide)
    have hpos : 0 < (Nat.card K)^2 := pow_pos Nat.card_pos 2
    omega
  let P : Sylow 2 Z := default
  have hi : ¬ 2 ∣ ((P : Subgroup Z).map Z.subtype).index := by
    rw [index_map_of_injective _ Z.subtype_injective,range_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hindex
  exact ⟨(P.isPGroup'.map Z.subtype).toSylow hi,map_subtype_le _⟩

/-- A quotient with exactly the entire short line as kernel separates
long-root conjugates, even though it kills the marked short involution. -/
theorem longClass_image_injective {J : Type*} [Group J] (f : C →* J)
    (hker : f.ker = (shortLine F σ hσ).subgroupOf C) :
    Set.InjOn f {x : C | IsConj (longMark F σ hσ) x} := by
  intro x hx y hy he
  obtain ⟨a,rfl⟩ := isConj_iff.mp hx
  obtain ⟨b,rfl⟩ := isConj_iff.mp hy
  obtain ⟨v,_,hv⟩ := conjugate_long F σ hσ a
  obtain ⟨w,_,hw⟩ := conjugate_long F σ hσ b
  rw [hv,hw] at he ⊢
  have hk : (rootPair F σ hσ v)⁻¹ * rootPair F σ hσ w ∈
      (shortLine F σ hσ).subgroupOf C := by
    rw [←hker,MonoidHom.mem_ker,map_mul,map_inv,he,inv_mul_cancel]
  obtain ⟨c,hc⟩ := hk
  have hc' : radicalHom F σ hσ (Multiplicative.ofAdd (lineParameter F σ c.toAdd)) =
      radicalHom F σ hσ ((Multiplicative.ofAdd (symmetric F σ (v.1^2) (v.1*v.2) (v.2^2)))⁻¹ *
        Multiplicative.ofAdd (symmetric F σ (w.1^2) (w.1*w.2) (w.2^2))) := by
    rw [map_mul,map_inv]
    exact hc
  have hh := congrArg Multiplicative.toAdd (radicalHom_injective F σ hσ hc')
  change lineParameter F σ c.toAdd =
    -(symmetric F σ (v.1^2) (v.1*v.2) (v.2^2)) +
      symmetric F σ (w.1^2) (w.1*w.2) (w.2^2) at hh
  have hvw : v = w := by
    apply Prod.ext
    · apply (frobeniusEquiv K 2).injective
      apply Subtype.ext
      have h0 := congrArg (fun X : hermitianMatrices F σ => X.val 0 0) hh
      change 0 = -(v.1 : F)^2 + (w.1 : F)^2 at h0
      change (v.1 : F)^2 = (w.1 : F)^2
      linear_combination h0
    · apply (frobeniusEquiv K 2).injective
      apply Subtype.ext
      have h1 := congrArg (fun X : hermitianMatrices F σ => X.val 1 1) hh
      change 0 = -(v.2 : F)^2 + (w.2 : F)^2 at h1
      change (v.2 : F)^2 = (w.2 : F)^2
      linear_combination h1
  rw [hvw]

/-- Each nonzero vector in the full-line quotient has exactly one lift in
the long-root class of the original residual short-root centralizer. -/
theorem existsUnique_long_lift {J : Type*} [Group J] (f : C →* J)
    (hker : f.ker = (shortLine F σ hσ).subgroupOf C)
    {v : J} (hv : v ∈ ((orthogonalRadical F σ hσ).subgroupOf C).map f)
    (hv1 : v ≠ 1) :
    ∃! x : C, IsConj (longMark F σ hσ) x ∧ f x = v := by
  obtain ⟨A,hA⟩ := orthogonal_image_fusion F σ hσ f hker.ge hv hv1
  let a := fixedLevi F σ hσ A
  have hx : IsConj (longMark F σ hσ) (a * longMark F σ hσ * a⁻¹) :=
    isConj_iff.mpr ⟨a,rfl⟩
  have he : f (a * longMark F σ hσ * a⁻¹) = v := by
    simpa only [map_mul,map_inv] using hA
  refine ⟨_,⟨hx,he⟩,?_⟩
  intro y hy
  exact longClass_image_injective F σ hσ f hker hy.1 hx (hy.2.trans he.symm)

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
