module
public import Theory.SpecificGroups.SU3.SmallSpecialThreeCore
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# The extraspecial three-core of SU3(2)

In an orthonormal basis the diagonal cubic and a three-cycle matrix have
order three and do not commute. The characteristic three-core has index
eight, so both matrices belong to it. Transport through actual Hermitian
basis changes proves that the original core, of order twenty-seven, is
extraspecial for every stored form.

Its center, derived subgroup and Frattini subgroup are exactly the original
scalar projection kernel. The projective self-centralizer calculation also
identifies its full centralizer in SU3(2). Consequently automorphisms
preserving an actual Sylow two-subgroup are detected on this three-core.
These are the inputs to the small special-unitary innerness argument.
Source: DGS, Groups and Graphs (1985), p.104 and 6.1, pp.118--119;
Huppert II.10.4 for the Hermitian basis changes.
-/

public noncomputable section
open Subgroup Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

private def orthogonalForm : HermitianForm 3 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := 1
  form_hermitian := by intro i j; fin_cases i <;> fin_cases j <;> simp
  form_nondegenerate := by simp

private def diagonalUnit (w : F) (hw : w^3=1) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero !![1,0,0;0,w,0;0,0,w^2] (by
    have hn : w ≠ 0 := by intro h; simp [h] at hw
    simp [det_fin_three,hn])
private def cycleUnit : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero !![0,0,1;1,0,0;0,1,0] (by simp [det_fin_three])

omit [Finite F] in
private theorem diagonal_cube (w : F) (hw : w^3=1) : diagonalUnit w hw ^ 3 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalUnit,GeneralLinearGroup.mkOfDetNeZero,pow_succ,
      Matrix.mul_apply,Fin.sum_univ_succ]
  · linear_combination hw
  · have hh := congrArg (fun z:F => z^2) hw
    linear_combination hh

omit [Finite F] in
private theorem cycle_cube : (cycleUnit : GL (Fin 3) F)^3=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleUnit,GeneralLinearGroup.mkOfDetNeZero,pow_succ,Matrix.mul_apply,Fin.sum_univ_succ]

omit [Finite F] in
private theorem diagonal_special (hconj : ∀ x, J.conj x=x^2)
    (w:F) (hw : w^3=1) : diagonalUnit w hw ∈ (orthogonalForm J).specialSubgroup := by
  rw [mem_specialSubgroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalUnit,GeneralLinearGroup.mkOfDetNeZero,orthogonalForm,
        conjTranspose,Matrix.mul_apply,Fin.sum_univ_succ,hconj]
    · linear_combination hw
    · have hh := congrArg (fun z:F => z^2) hw
      linear_combination hh
  · apply Units.ext
    change (!![1,0,0;0,w,0;0,0,w^2] : Matrix (Fin 3) (Fin 3) F).det = 1
    simpa [det_fin_three,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hw

omit [Finite F] in
private theorem cycle_special : (cycleUnit : GL (Fin 3) F) ∈ (orthogonalForm J).specialSubgroup := by
  rw [mem_specialSubgroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleUnit,GeneralLinearGroup.mkOfDetNeZero,orthogonalForm,
        conjTranspose,Matrix.mul_apply,Fin.sum_univ_succ]
  · apply Units.ext
    change (!![0,0,1;1,0,0;0,1,0] : Matrix (Fin 3) (Fin 3) F).det = 1
    simp [det_fin_three]

/-- The full degree-one special unitary group has order 216. -/
theorem special_group_card (hc : Nat.card F=2^2) (hconj : ∀ x,J.conj x=x^2) :
    Nat.card J.specialSubgroup = 216 := by
  rw [J.specialToProjective.ker.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
      J.specialToProjective_surjective).toEquiv,
    special_scalar_kernel_card J hc hconj,FixedFieldTwo.card_projective J hc hconj]

private theorem cube_mem_core (hc : Nat.card F=2^2) (hconj : ∀ x,J.conj x=x^2)
    (x : J.specialSubgroup) (hx : x^3=1) : x ∈ pCore 3 J.specialSubgroup := by
  let N := pCore 3 J.specialSubgroup
  have hq : Nat.card (J.specialSubgroup ⧸ N) = 8 := by
    have hh := N.card_mul_index
    rw [special_core_card J hc hconj,special_group_card J hc hconj,index_eq_card] at hh
    omega
  have hcop : Nat.Coprime (Nat.card (J.specialSubgroup ⧸ N)) 3 := by rw [hq]; decide
  apply (QuotientGroup.eq_one_iff _).mp
  apply hcop.pow_left_bijective.injective
  change (QuotientGroup.mk' N x)^3 = (1:J.specialSubgroup ⧸ N)^3
  rw [←map_pow,hx,map_one,one_pow]

private theorem orthogonal_core_noncommutative
    (hc : Nat.card F=2^2) (hconj : ∀ x,J.conj x=x^2) :
    ¬ IsMulCommutative (pCore 3 (orthogonalForm J).specialSubgroup) := by
  have hu : Nat.card Fˣ = 3 := by rw [Nat.card_units,hc]; decide
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w,hwn⟩ := exists_ne (1:Fˣ)
  have hw : (w:F)^3=1 := by
    have hh := pow_card_eq_one' (x:=w)
    rw [hu] at hh
    exact congrArg Units.val hh
  let K := orthogonalForm J
  let d : K.specialSubgroup := ⟨diagonalUnit (w:F) hw,diagonal_special J hconj _ hw⟩
  let c : K.specialSubgroup := ⟨cycleUnit,cycle_special J⟩
  have hd : d ∈ pCore 3 K.specialSubgroup := cube_mem_core K hc hconj d (Subtype.ext (diagonal_cube _ hw))
  have hcm : c ∈ pCore 3 K.specialSubgroup := cube_mem_core K hc hconj c (Subtype.ext cycle_cube)
  intro hab
  have he := congrArg (fun z : pCore 3 K.specialSubgroup => z.val.val.val 1 0)
    (hab.is_comm.comm (⟨d,hd⟩ : pCore 3 K.specialSubgroup) ⟨c,hcm⟩)
  apply hwn
  apply Units.ext
  simpa [d,c,diagonalUnit,cycleUnit,GeneralLinearGroup.mkOfDetNeZero,
    Matrix.mul_apply,Fin.sum_univ_succ] using he

/-- The actual SU₃(2) three-core is extraspecial, for every Hermitian form. -/
theorem special_core_extraspecial (hc : Nat.card F=2^2) (hconj : ∀ x,J.conj x=x^2) :
    IsExtraspecial 3 (pCore 3 J.specialSubgroup) := by
  let K := orthogonalForm J
  have hf : Nat.card {x:F // J.conj x=x}=2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hc) (by simpa using hconj)
  obtain ⟨C,hC⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis J 2 hc hf
  obtain ⟨D,hD⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis K 2 hc hf
  let e : J.specialSubgroup ≃* K.specialSubgroup :=
    (OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC).trans
      (OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv K D hD).symm
  let eN := ((pCore 3 J.specialSubgroup).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 3 e))
  apply IsExtraspecial.of_noncommutative_card_prime_cube (by simpa using special_core_card J hc hconj)
  intro hn
  let := hn
  apply orthogonal_core_noncommutative J hc hconj
  refine ⟨⟨?_⟩⟩
  intro a b
  obtain ⟨a,rfl⟩ := eN.surjective a
  obtain ⟨b,rfl⟩ := eN.surjective b
  exact (map_mul eN a b).symm.trans ((congrArg eN (hn.is_comm.comm a b)).trans (map_mul eN b a))
/-- The scalar denominator is exactly the center of the actual special three-core. -/
theorem special_core_center (hc : Nat.card F=2^2) (hconj : ∀ x,J.conj x=x^2) :
    center (pCore 3 J.specialSubgroup) = (specialCoreProjection J).ker := by
  let := special_core_extraspecial J hc hconj
  exact (eq_of_le_of_card_ge (specialCoreProjection_ker_central J)
    (by rw [IsExtraspecial.center_order_p 3 _,specialCoreProjection_ker_card J hc hconj])).symm

/-- The scalar denominator is also the derived subgroup. -/
theorem special_core_derived (hc : Nat.card F=2^2) (hconj : ∀ x,J.conj x=x^2) :
    commutator (pCore 3 J.specialSubgroup) = (specialCoreProjection J).ker := by
  let := special_core_extraspecial J hc hconj
  exact (IsExtraspecial.commutator_eq_center (p:=3)).trans (special_core_center J hc hconj)

/-- The scalar denominator is also the Frattini subgroup. -/
theorem special_core_frattini (hc : Nat.card F=2^2) (hconj : ∀ x,J.conj x=x^2) :
    frattini (pCore 3 J.specialSubgroup) = (specialCoreProjection J).ker := by
  let := special_core_extraspecial J hc hconj
  exact (IsExtraspecial.frattini_eq_center (p:=3)).trans (special_core_center J hc hconj)

/-- Its centralizer in the full special-unitary group is the same original scalar kernel. -/
theorem special_core_centralizer (hc : Nat.card F=2^2) (hconj : ∀ x,J.conj x=x^2) :
    centralizer (pCore 3 J.specialSubgroup : Set J.specialSubgroup) = J.specialToProjective.ker := by
  apply le_antisymm
  · intro x hx
    have hm : J.specialToProjective x ∈ pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) := by
      rw [←(projective_core_structure J hc hconj).2.2]
      intro y hy
      obtain ⟨z,hz⟩ := specialCoreProjection_surjective J ⟨y,hy⟩
      have hh := congrArg Subtype.val hz
      change J.specialToProjective z.val = y at hh
      rw [←hh,←map_mul,←map_mul,hx z.val z.property]
    have hxN : x ∈ pCore 3 J.specialSubgroup := by
      rw [←special_core_preimage J]; exact hm
    have hxZ : (⟨x,hxN⟩ : pCore 3 J.specialSubgroup) ∈ center _ :=
      mem_center_iff.mpr fun y => Subtype.ext (hx y.val y.property)
    rw [special_core_center J hc hconj] at hxZ
    exact congrArg Subtype.val hxZ
  · intro x hx y _
    exact mem_center_iff.mp (J.specialToProjective_ker_le_center hx) y

/-- A special-unitary automorphism preserving an actual Sylow two-subgroup is detected on the characteristic three-core. -/
theorem special_aut_eq_one_of_core_and_sylow (hc : Nat.card F=2^2)
    (hconj : ∀ x,J.conj x=x^2) (T:Sylow 2 J.specialSubgroup)
    (a:MulAut J.specialSubgroup) (hT:(T:Subgroup J.specialSubgroup).map a.toMonoidHom=T)
    (hfix:∀ n ∈ pCore 3 J.specialSubgroup, a n=n) : a=1 := by
  let N := pCore 3 J.specialSubgroup
  have hTc : Nat.card T=8 := by
    rw [T.card_eq_multiplicity,special_group_card J hc hconj]; decide +kernel
  have hcomp : N.IsComplement' (T:Subgroup J.specialSubgroup) := isComplement'_of_coprime
    (by rw [special_core_card J hc hconj,hTc,special_group_card J hc hconj])
    (by rw [special_core_card J hc hconj,hTc]; decide)
  have hfixT (t:J.specialSubgroup) (ht:t∈T) : a t=t := by
    have hd : t⁻¹*a t ∈ centralizer (N:Set _) := by
      intro n hn
      have he := hfix (t*n*t⁻¹) ((inferInstance:N.Normal).conj_mem n hn t)
      rw [map_mul,map_mul,map_inv,hfix n hn] at he
      calc
        n*(t⁻¹*a t) = t⁻¹*(t*n*t⁻¹)*a t := by group
        _ = t⁻¹*(a t*n*(a t)⁻¹)*a t := congrArg (fun x => t⁻¹*x*a t) he.symm
        _ = (t⁻¹*a t)*n := by group
    rw [special_core_centralizer J hc hconj] at hd
    have haT : a t ∈ (T:Subgroup J.specialSubgroup) := hT ▸ mem_map_of_mem a.toMonoidHom ht
    have he : t⁻¹*a t=1 := mem_bot.mp (hcomp.disjoint.le_bot
      ⟨scalar_kernel_le_special_core J hd,(T:Subgroup J.specialSubgroup).mul_mem ((T:Subgroup J.specialSubgroup).inv_mem ht) haT⟩)
    exact (inv_mul_eq_one.mp he).symm
  have he : N ⊔ (T:Subgroup J.specialSubgroup) ≤ a.toMonoidHom.eqLocus (MonoidHom.id _) := sup_le hfix hfixT
  exact MulEquiv.ext fun x => he (hcomp.sup_eq_top ▸ mem_top x)

end BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
