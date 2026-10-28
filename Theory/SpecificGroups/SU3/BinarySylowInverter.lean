module
public import Theory.SpecificGroups.PSL2.BinarySplitInverter
public import Theory.SpecificGroups.SU3.BinaryInvolutionTable
public import Theory.SpecificGroups.SU3.SylowPointwiseInner
public import Theory.GroupAction.InvertedPrimeLift
public import Theory.GroupAction.PerfectCentralQuotientSylow
public import Theory.GroupTheory.AutomorphismOvergroupCore
/-!
# Split-torus inversion for binary unitary Sylow fixers

Every inner involution is conjugate into the long-root subgroup, which
lies in the actual graph-fixed PSL₂ of the fixed field. Its reflected
torus supplies inverted elements of every prime order dividing q−1.
The root-fixed calculation adapts `GraphFixedSylowCenters.lean`.

For a perfect central cover, the prescribed Sylow fixer descends
faithfully to the projective unitary group and is inner. A genuine
Hermitian basis change and the fixed-kernel inversion lift retain the
original actor and the prime order upstairs. No splitting of the center
or replacement of the original action is assumed.

Source: Aschbacher--Smith 12.6.26, printed p.832; Huppert II.8.3,
II.10.12 and the binary Sylow-fixer calculation in `SylowPointwiseInner`.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BinarySylowInverter
open OddPrimeSylow.NormalizedOuter.Coverage
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem root_fixed_of_fst_zero (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    hermitianUnipotentPSU J hJ z ∈ (J.projectiveGraphAut hJ).fixedSubgroup := by
  have hb : J.conj z.val.2 = z.val.2 := by
    have ht := z.property
    simp only [hz,map_zero,zero_mul,add_zero] at ht
    exact (eq_neg_of_add_eq_zero_right ht).trans (CharTwo.neg_eq _)
  have hp : hermitianUnipotentPSU J hJ z =
      J.specialToProjective (hermitianUnipotentSU J hJ z) := by
    apply Subtype.ext
    rw [hermitianUnipotentPSU_val,specialToProjective_apply_val]
    rfl
  rw [MulAut.mem_fixedSubgroup,hp,J.projectiveGraphAut_specialToProjective hJ]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [specialGraphAut_apply_val]
  change (hermitianUnipotentMatrix J z).map J.conj = hermitianUnipotentMatrix J z
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianUnipotentMatrix,hz,hb]

/-- In standard Hermitian coordinates an inner involution inverts every prime divisor of q−1. -/
theorem inner_involution_inverts_split_prime
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n p : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n)^2)
    (hf : Nat.card {x : F // J.conj x = x} = 2 ^ n)
    (hp : p.Prime) (hd : p ∣ 2 ^ n - 1)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    ∃ x : ProjectiveSpecialUnitaryMatrixGroup J,
      orderOf x = p ∧ t*x*t⁻¹=x⁻¹ := by
  obtain ⟨g,z,hz,he,_,_⟩ := BinaryInvolutionTable.involution_root_geometry J hJ hn hF hf t ht
  let W := (J.projectiveGraphAut hJ).fixedSubgroup
  let r : W := ⟨hermitianUnipotentPSU J hJ z,root_fixed_of_fst_zero J hJ z hz⟩
  have hr : orderOf r = 2 := by
    rw [←Subgroup.orderOf_coe]
    change orderOf (root J hJ z) = 2
    rw [←he,MulEquiv.orderOf_eq,ht]
  let e := J.projectiveGraphFixedEquiv hJ
  obtain ⟨x,hx,hi⟩ := Theory.PSL2.binary_involution_inverts_split_prime
    (by omega : 0 < n) (show Nat.card (FixedBy.subfield F J.conj) = 2^n from hf)
    hp hd (e r) ((e.orderOf_eq r).trans hr)
  let y := e.symm x
  have hy : orderOf (y : ProjectiveSpecialUnitaryMatrixGroup J) = p := by
    rw [Subgroup.orderOf_coe]
    exact (e.symm.orderOf_eq x).trans hx
  have hyi : (root J hJ z) * y.val * (root J hJ z)⁻¹ = y.val⁻¹ := by
    have hh := congrArg (fun b => (e.symm b).val) hi
    simpa only [map_mul,map_inv,e.symm_apply_apply,Subgroup.coe_mul,Subgroup.coe_inv] using hh
  refine ⟨(MulAut.conj g).symm y.val,((MulAut.conj g).symm.orderOf_eq y.val).trans hy,?_⟩
  apply (MulAut.conj g).injective
  simpa only [map_mul,map_inv,MulEquiv.apply_symm_apply,he] using hyi

/-- The prescribed Sylow fixer on a perfect central cover inverts split-torus primes upstairs. -/
theorem sylow_fixer_inverts_split_prime_of_fixes_center
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    [IsSimpleGroup (B ⧸ center B)]
    (J : HermitianForm 3 F) {n p : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = (2^n)^2) (hc : ∀ x, J.conj x = x^(2^n))
    (e : B ⧸ center B ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (a : MulAut B) (ha : orderOf a = 2)
    (P : Sylow 2 B) (hP : ∀ x ∈ P, a x = x)
    (hZ : ∀ x ∈ center B, a x = x) (hp : p.Prime)
    (ho : Odd p) (hd : p ∣ 2^n-1) :
    ∃ x : B, orderOf x = p ∧ a x = x⁻¹ := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hc
  obtain ⟨d⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hF hf
  let J₀ := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let e₀ := e.trans d
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) := Finite.of_equiv _ e₀.toEquiv
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := e₀.symm.isSimpleGroup
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Group.IsPerfect.ofSurjective (f := e₀.toMonoidHom.comp (QuotientGroup.mk' (center B)))
      (e₀.surjective.comp (QuotientGroup.mk'_surjective _))
  let b := MulAut.centralQuotientAction e₀ a
  have hb : orderOf b = 2 :=
    (orderOf_injective _ (MulAut.centralQuotientAction_injective e₀) a).trans ha
  obtain ⟨Q,hQ⟩ := MulAut.centralQuotientAction_exists_fixed_sylow e₀ a P hP
  obtain ⟨t,ht⟩ := SylowPointwiseInner.involutive_fixing_sylow_inner J₀ rfl hn hF hc
    Q b (hb ▸ pow_orderOf_eq_one b) hQ
  have htc : orderOf t = 2 :=
    (orderOf_injective MulAut.conj
      (Theory.GroupTheory.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect) t).symm.trans
      (ht ▸ hb)
  obtain ⟨y,hy,hi⟩ := inner_involution_inverts_split_prime J₀ rfl hn hF hf hp hd t htc
  let f := e₀.toMonoidHom.comp (QuotientGroup.mk' (center B))
  apply MulAut.exists_inverted_prime_of_fixed_kernel a b f
    (e₀.surjective.comp (QuotientGroup.mk'_surjective _))
    (fun x => (MulAut.centralQuotientAction_apply e₀ a x).symm)
    (ha ▸ pow_orderOf_eq_one a) ?_ hp ho y hy ?_
  · intro x hx
    apply hZ x
    apply (QuotientGroup.eq_one_iff _).mp
    apply e₀.injective
    exact hx.trans e₀.map_one.symm
  · rw [ht]
    exact hi
end BenderSuzuki.MatrixGroups.HermitianForm.BinarySylowInverter
