module

public import Theory.SpecificGroups.OrthogonalFourBinary.OmegaResidualGeometry
public import Theory.GroupTheory.PResidual.NormalComplement

/-!
# A cubic fixer on the fixed plane of a full Omega inverter

An involution whose commutator with the odd core is the whole odd core
inverts that core, since it is elementary abelian. The two independent
rotations lie in the odd core. In the actual 72-isometry coordinates,
inverting both rotations forces the involution to fix a nonzero vector in
one definite plane; the rotation of the other plane fixes that vector.
The witness is an actual element of order three in the Siegel-generated Omega.

The finite check retains the square-one condition: the two displayed inversion
equations alone admit additional coordinate solutions.
Source: Aschbacher--Smith, 15.2.25(1), printed p.1118, using 15.2.13(2).
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement

private theorem abelian_full_commutator_inverted {D : Type*} [Group D]
    (R : Subgroup D) [R.Normal] [IsMulCommutative R]
    (b : D) (hb : orderOf b = 2) (hc : ⁅R,zpowers b⁆ = R) :
    ∀ r ∈ R, b*r*b⁻¹ = r⁻¹ := by
  have hb2 : b^2=1 := by simpa only [hb] using pow_orderOf_eq_one b
  have hbi : b⁻¹=b := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hb2)
  have memB (a : D) (ha : a ∈ zpowers b) : a=1 ∨ a=b := by
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp ha
    have he : b^n=b^(n%2) := by simpa [hb] using (zpow_mod_orderOf b n).symm
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left; rw [he,h]; simp
    · right; rw [he,h]; simp
  intro r hr
  have hr' : r ∈ ⁅R,zpowers b⁆ := hc.symm ▸ hr
  change r ∈ Subgroup.closure _ at hr'
  clear hr
  have hh : (MulAut.conj b) r = r⁻¹ := by
    induction hr' using closure_induction with
    | mem x hx =>
      obtain ⟨y,hy,a,ha,rfl⟩ := hx
      rcases memB a ha with ha1 | hab
      · rw [ha1]; simp
      · rw [hab]
        change b * ⁅y,b⁆ * b⁻¹ = ⁅y,b⁆⁻¹
        simp only [commutatorElement_def,mul_inv_rev,inv_inv]
        calc
          b * (y*b*y⁻¹*b⁻¹) * b⁻¹ = b*y*b*y⁻¹*(b⁻¹*b⁻¹) := by group
          _ = b*y*b*y⁻¹ := by rw [hbi,←pow_two,hb2,mul_one]
          _ = b*(y*(b⁻¹*y⁻¹)) := by rw [hbi]; group
    | one => simp
    | mul x y hx hy ihx ihy =>
      rw [map_mul,ihx,ihy,mul_inv_rev]
      have hxR : x∈R := commutator_le_left _ _ hx
      have hyR : y∈R := commutator_le_left _ _ hy
      exact congrArg Subtype.val (mul_comm (⟨x⁻¹,R.inv_mem hxR⟩ : R) ⟨y⁻¹,R.inv_mem hyR⟩)
    | inv x hx ih => rw [map_inv,ih]
  exact hh

namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines
set_option synthInstance.maxSize 10000

private def rL : omega := ⟨codeMap leftRotation,generators_mem_omega.1⟩
private def rR : omega := ⟨codeMap rightRotation,generators_mem_omega.2.1⟩

private theorem rotations_cube : rL^3=1 ∧ rR^3=1 := by
  constructor <;> apply Subtype.ext <;> apply Subtype.ext <;> apply LinearEquiv.ext <;>
    intro v
  · change candidate leftRotation (candidate leftRotation (candidate leftRotation v))=v
    simp only [candidate_eval]
    exact (show ∀v:Space,eval leftRotation (eval leftRotation (eval leftRotation v))=v by decide +kernel) v
  · change candidate rightRotation (candidate rightRotation (candidate rightRotation v))=v
    simp only [candidate_eval]
    exact (show ∀v:Space,eval rightRotation (eval rightRotation (eval rightRotation v))=v by decide +kernel) v

private theorem rR_order : orderOf rR=3 := by
  apply orderOf_eq_prime rotations_cube.2
  intro he
  have h := congrArg (fun a:omega => a.val.val ((0,0),(1,0))) he
  change candidate rightRotation ((0,0),(1,0))=((0,0),(1,0)) at h
  rw [candidate_eval] at h
  exact (by decide +kernel : eval rightRotation ((0,0),(1,0))≠((0,0),(1,0))) h

private def inversionTest (k:Code) : Prop :=
  (∀v:Space,eval k (eval k v)=v) ∧
  (∀v:Space,eval k (eval leftRotation (eval k v))=eval leftRotation (eval leftRotation v)) ∧
  (∀v:Space,eval k (eval rightRotation (eval k v))=eval rightRotation (eval rightRotation v))
private instance (k:Code) : Decidable (inversionTest k) := inferInstanceAs (Decidable (_ ∧ _))
private theorem fixed_cubic_table : ∀ k:Code, inversionTest k →
    ∃ v:Space,v≠0 ∧ eval k v=v ∧ eval rightRotation v=v := by decide +kernel

theorem inverting_involution_plane_has_cubic_fixer (b:omega) (hb:orderOf b=2)
    (hc:⁅pPrimeCore 2 omega,zpowers b⁆=pPrimeCore 2 omega) :
    ∃ (v:Space) (a:omega),v≠0 ∧ b.val.val v=v ∧ orderOf a=3 ∧ a.val.val v=v := by
  let R:=pPrimeCore 2 omega
  have hle : R≤pResidual 2 omega := pPrimeCore_le_pResidual
  let : IsElementaryAbelian 3 (pResidual 2 omega) := omega_twoResidual_elementary
  let : IsElementaryAbelian 3 R := IsElementaryAbelian.of_injective
    (inclusion hle) (inclusion_injective hle)
  have hres : pResidual 2 omega ≤ R := by
    apply le_sSup
    exact ⟨inferInstance,(Nat.coprime_two_left.mpr
      (odd_twoResidual_of_injective omega.subtype Subtype.val_injective))⟩
  have hinv (a:omega) (ha:a^3=1) : b*a*b⁻¹=a⁻¹ :=
    abelian_full_commutator_inverted R b hb hc a (hres
      (mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
        (orderOf_dvd_of_pow_eq_one ha))))
  obtain ⟨k,hk⟩ := codeMap_bijective.surjective b.val
  have hbi : b⁻¹=b := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using (show b^2=1 by simpa only [hb] using pow_orderOf_eq_one b))
  have hv (a:omega) (ha:a^3=1) (v:Space) :
      b.val.val (a.val.val (b.val.val v))=a.val.val (a.val.val v) := by
    have he : a⁻¹=a*a := inv_eq_of_mul_eq_one_right (by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using ha)
    have hh := hinv a ha
    rw [hbi,he] at hh
    exact congrArg (fun a:omega=>a.val.val v) hh
  have ht : inversionTest k := by
    refine ⟨?_,?_,?_⟩
    · intro v
      have hh := congrArg (fun a:omega=>a.val.val v)
        (show b^2=1 by simpa only [hb] using pow_orderOf_eq_one b)
      change b.val.val (b.val.val v)=v at hh
      rw [←hk] at hh
      simpa only [codeMap,candidate_eval] using hh
    · intro v
      have hh:=hv rL rotations_cube.1 v
      rw [←hk] at hh
      simpa only [rL,codeMap,candidate_eval] using hh
    · intro v
      have hh:=hv rR rotations_cube.2 v
      rw [←hk] at hh
      simpa only [rR,codeMap,candidate_eval] using hh
  obtain ⟨v,hv,hbV,haV⟩:=fixed_cubic_table k ht
  refine ⟨v,rR,hv,?_,rR_order,?_⟩
  · rw [←hk]
    exact (candidate_eval k v).trans hbV
  · exact (candidate_eval rightRotation v).trans haV
end OrthogonalFourBinary.SylowGeometry
