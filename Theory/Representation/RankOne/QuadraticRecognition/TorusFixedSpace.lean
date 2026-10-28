module
public import Theory.Representation.RankOne.QuadraticRecognition.FixedGeneratedReduction
public import Theory.SpecificGroups.SU3.MarkedFiveTorus
public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots.Coordinates

/-!
# Detection of the unitary norm-one torus on the local module

For a quadratic binary actor A, its displacements lie in C_V(A). If an
odd-order element k commutes with A and fixes C_V(A), the commuting-operator
identity puts every k-displacement in C_V(A). Thus (ρ(k)−1)²=0. In
characteristic two ρ(k)²=1, and its odd order forces ρ(k)=1.
Faithfulness therefore detects each nonidentity such k already on C_V(A).

The special norm-one torus commutes with the literal central root by its
matrix formula. Its order is q+1, which is odd. The projective application
uses the actual torus map, whose cubic scalar kernel remains explicit.
Both applications give movement on the fixed-generated fixed-field SL₂
block, with no irreducibility or global generation premise.

This excludes centralization of the whole local block in the faithful
version of the first torus branch of DGS85 (5.10)(b), printed p.112.
It does not infer fixed-point-free action on the local central quotient;
that stronger inference and the ensuing numerical reduction remain to be
proved. CriticalTorusDetection applies the result to Z/(Z∩Z(L)).
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.RankOne.QuadraticRecognition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- An odd-order element commuting with a quadratic actor is detected on
that actor's fixed space. -/
theorem odd_centralizer_trivial_of_fixes_fixedSpace
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (hq : IsQuadratic ρ A)
    (k : G) (hc : k ∈ centralizer (A : Set G))
    {m : ℕ} (hm : Odd m) (hk : k^m=1)
    (hfix : ∀ v ∈ fixedSpace ρ A, ρ k v=v) : ρ k=1 := by
  have hdisp (v : V) : ρ k v-v ∈ fixedSpace ρ A := by
    intro a
    have ha : ρ a v-v ∈ fixedSpace ρ A := fun b => hq b b.property a a.property v
    have he := hfix (ρ a v-v) ha
    rw [map_sub] at he
    have hcomm : ρ k (ρ a v)=ρ a (ρ k v) := by
      rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,hc a a.property]
    rw [hcomm] at he
    change ρ a (ρ k v-v)=ρ k v-v
    rw [map_sub]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp he
  have hsquare : (ρ k)^2=1 := by
    ext v
    have he := hfix (ρ k v-v) (hdisp v)
    rw [map_sub] at he
    have htwo (w : V) : w+w=0 := by
      calc
        w+w=((1:ZMod 2)+1) • w := by rw [add_smul,one_smul]
        _=0 := by rw [show (1:ZMod 2)+1=0 by decide,zero_smul]
    have he' : ρ k (ρ k v)+v=ρ k v+ρ k v := (sub_eq_sub_iff_add_eq_add.mp he)
    rw [htwo] at he'
    have hv := (add_right_cancel_iff (a := v)).mp (he'.trans (htwo v).symm)
    simpa only [pow_two,Module.End.mul_apply,Module.End.one_apply] using hv
  obtain ⟨r,hr⟩ := hm
  have he := congrArg ρ hk
  rw [map_pow,map_one,hr,pow_add,pow_mul,hsquare,one_pow,pow_one,one_mul] at he
  exact he

/-- Faithfulness detects every nonidentity odd centralizer element already
on C_V(A), without a global fixed-space-generation assumption. -/
theorem exists_fixedSpace_moved_by_odd_centralizer
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (A : Subgroup G) (hq : IsQuadratic ρ A)
    (k : G) (hc : k ∈ centralizer (A : Set G))
    {m : ℕ} (hm : Odd m) (hk : k^m=1) (hne : k≠1) :
    ∃ v ∈ fixedSpace ρ A, ρ k v≠v := by
  by_contra! hh
  exact hne (hf ((odd_centralizer_trivial_of_fixes_fixedSpace ρ A hq k hc hm hk hh).trans
    ρ.map_one.symm))

open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus.EvenCenterAction HermitianForm.EvenInner
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem normOne_odd_power (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0<n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n)) (k : normOne J) :
    Odd (2^n+1) ∧ k^(2^n+1)=1 := by
  refine ⟨(even_two.pow_of_ne_zero (by omega : n≠0)).add_odd odd_one,?_⟩
  rw [←normOne_card J hcard hconj]
  exact pow_card_eq_one'

omit [Finite F] in
private theorem special_normOne_centralizes_central (J : HermitianForm 3 F)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0]) (k : normOne J) :
    hermitianTorusSU J hJ k.val ∈ centralizer (central J hJ : Set _) := by
  rintro _ ⟨b,rfl⟩
  have he : hermitianTorusAction J k.val (centralCoord J b)=centralCoord J b := by
    apply Subtype.ext
    apply Prod.ext
    · change 0*(k.val:F)*(J.conj (k.val:F))⁻¹^2=0
      simp only [zero_mul]
    · change (b.toAdd:F)*(J.conj (k.val:F))⁻¹*(k.val:F)⁻¹=(b.toAdd:F)
      rw [k.property,inv_inv,mul_inv_cancel_right₀ k.val.ne_zero]
  apply Subtype.ext
  symm
  change hermitianTorusGL J k.val * hermitianUnipotentGL J (centralCoord J b) =
    hermitianUnipotentGL J (centralCoord J b) * hermitianTorusGL J k.val
  rw [hermitianTorusGL_mul_unipotent,he]

/-- The genuine special norm-one torus is detected on the quadratic actor's
fixed space, including its possible cubic scalar elements. -/
theorem su3_normOne_moves_actor_fixedSpace
    (J : HermitianForm 3 F) (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 0<n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (hf : Function.Injective ρ)
    (A : Subgroup J.specialSubgroup) (hA : A≤central J hJ) (hq : IsQuadratic ρ A)
    (k : normOne J) (hk : hermitianTorusSU J hJ k.val ≠ 1) :
    ∃ v ∈ fixedSpace ρ A, ρ (hermitianTorusSU J hJ k.val) v≠v := by
  obtain ⟨ho,hpow⟩ := normOne_odd_power J hn hcard hconj k
  apply exists_fixedSpace_moved_by_odd_centralizer ρ hf A hq _
    ((centralizer_le hA) (special_normOne_centralizes_central J hJ k)) ho _ hk
  exact (map_pow ((hermitianTorusSU J hJ).comp (normOne J).subtype) k (2^n+1)).symm.trans
    (by rw [hpow,map_one])

/-- In PSU₃, nontriviality is tested after the canonical cubic scalar
quotient, on the original norm-one torus image. -/
theorem psu3_normOne_moves_actor_fixedSpace
    (J : HermitianForm 3 F) (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 0<n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hf : Function.Injective ρ)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A≤centralImage J hJ) (hq : IsQuadratic ρ A)
    (k : normOne J) (hk : normOneMap J hJ k ≠ 1) :
    ∃ v ∈ fixedSpace ρ A, ρ (normOneMap J hJ k) v≠v := by
  obtain ⟨ho,hpow⟩ := normOne_odd_power J hn hcard hconj k
  apply exists_fixedSpace_moved_by_odd_centralizer ρ hf A hq _
    ((centralizer_le hA) (HermitianForm.MarkedFiveTorus.normOne_centralizes_upper J hJ
      (show normOneMap J hJ k∈normOneImage J hJ from ⟨k,rfl⟩))) ho _ hk
  rw [←map_pow,hpow,map_one]

/-- No nonidentity special norm-one torus element centralizes the entire
fixed-generated block. The ambient representation need not be irreducible. -/
theorem su3_normOne_moves_fixedGenerated
    (J : HermitianForm 3 F) (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 0<n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (hf : Function.Injective ρ)
    (A : Subgroup J.specialSubgroup) (hA : A≤central J hJ) (hq : IsQuadratic ρ A)
    (k : normOne J) (hk : hermitianTorusSU J hJ k.val ≠ 1) :
    ∃ v ∈ (fixedGeneratedSubrepresentation (ρ.comp (block J hJ))
      (A.comap (block J hJ))).toSubmodule, ρ (hermitianTorusSU J hJ k.val) v≠v := by
  obtain ⟨v,hv,hm⟩ := su3_normOne_moves_actor_fixedSpace J hJ hn hcard hconj ρ hf A hA hq k hk
  exact ⟨v,fixedSpace_le_fixedGenerated _ _ (fun a => hv ⟨block J hJ a,a.property⟩),hm⟩

/-- The projective local module detects the exact projective torus image,
so cubic scalar elements are not mistaken for nontrivial actors. -/
theorem psu3_normOne_moves_fixedGenerated
    (J : HermitianForm 3 F) (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 0<n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hf : Function.Injective ρ)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A≤centralImage J hJ) (hq : IsQuadratic ρ A)
    (k : normOne J) (hk : normOneMap J hJ k ≠ 1) :
    let j := J.specialToProjective.comp (block J hJ)
    ∃ v ∈ (fixedGeneratedSubrepresentation (ρ.comp j) (A.comap j)).toSubmodule,
      ρ (normOneMap J hJ k) v≠v := by
  obtain ⟨v,hv,hm⟩ := psu3_normOne_moves_actor_fixedSpace J hJ hn hcard hconj ρ hf A hA hq k hk
  exact ⟨v,fixedSpace_le_fixedGenerated _ _
    (fun a => hv ⟨(J.specialToProjective.comp (block J hJ)) a,a.property⟩),hm⟩

end Representation.RankOne.QuadraticRecognition
