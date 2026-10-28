module
public import Theory.SpecificGroups.SU3.SylowPointwiseInner.Full
public import Theory.SpecificGroups.SU3.BorelCoprimeFieldAction
public import Theory.SpecificGroups.SU3.BorelTorus.EvenCenterAction
public import Theory.SpecificGroups.SU3.BinaryFixedTorusGeneration
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# A two-perfect subgroup of the binary unitary Borel

The Hermitian root group together with the torus on fixed-field units is
two-perfect: a nonidentity fixed unit has invertible first-coordinate
displacement, and squares recover the central root layer. A pointwise
automorphism fixer is root-inner by the actual semilinear Sylow-fixer
theorem; the fixed torus then forces both root coordinates to vanish.
These are the model ingredients for the ordinary unitary branch of
Aschbacher--Smith 15.1.21(iii), printed pp.1097--1098. We use this concrete
subgroup directly, without identifying it with the source's torsion-generated
subgroup or assuming Thompson normalization.
-/

public section
open Subgroup Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OrdinaryBorel
open BorelTorus BorelTorus.EvenCenterAction
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
/-- Inclusion of the actual fixed-field units into the matrix field. -/
@[expose] def fixedUnit : (fixedField J)ˣ →* Eˣ := Units.map (fixedField J).subtype.toMonoidHom
/-- The projective matrix torus on the fixed-field units. -/
@[expose] def fixedTorus : (fixedField J)ˣ →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (hermitianTorusPSU J hJ).comp (fixedUnit J)
/-- The literal root group joined with the fixed-field torus. -/
@[expose] def rootFixedTorus : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  projectiveRoot J hJ ⊔ (fixedTorus J hJ).range

private theorem fixedUnit_conj (k : (fixedField J)ˣ) : J.conj ((fixedUnit J k : Eˣ) : E) = (fixedUnit J k : Eˣ) := k.val.property
private theorem fixedUnit_ne_one {k : (fixedField J)ˣ} (hk : k ≠ 1) :
    ((fixedUnit J k : Eˣ) : E) ≠ 1 := by
  intro he
  exact hk (Units.ext (Subtype.ext he))

private theorem fixed_weight {k : (fixedField J)ˣ} (hk : k ≠ 1) :
    ((fixedUnit J k : Eˣ) : E) * (J.conj ((fixedUnit J k : Eˣ) : E))⁻¹ ^ 2 ≠ 1 := by
  rw [fixedUnit_conj]
  have hv := (fixedUnit J k).ne_zero
  have he : ((fixedUnit J k : Eˣ) : E) * ((fixedUnit J k : Eˣ) : E)⁻¹ ^ 2 =
      ((fixedUnit J k : Eˣ) : E)⁻¹ := by field_simp
  rw [he]
  exact inv_ne_one.mpr (fixedUnit_ne_one J hk)

private theorem exists_fixed_unit [Finite E] {q : ℕ}
    (hfixed : Nat.card {x : E // J.conj x = x} = q) (hq : 2<q) :
    ∃ k : (fixedField J)ˣ, k ≠ 1 := by
  have hc : 1 < Nat.card (fixedField J)ˣ := by rw [Nat.card_units]; change 1 < Nat.card {x : E // J.conj x=x}-1; omega
  let : Nontrivial (fixedField J)ˣ := Finite.one_lt_card_iff_nontrivial.mp hc
  exact exists_ne 1

variable [Finite E] [CharP E 2]

/-- This concrete Borel subgroup is two-perfect for every q = 2ⁿ ≥ 4. -/
theorem rootFixedTorus_twoPerfect {n : ℕ} (hn : 2≤n)
    (hcard : Nat.card E=(2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x=x}=2^n) :
    IsPPerfect 2 (rootFixedTorus J hJ) := by
  let B := rootFixedTorus J hJ
  let f : hermitianUnipotentCoord J →* B := (hermitianUnipotentPSU J hJ).codRestrict B
    (fun z => (show projectiveRoot J hJ ≤ B from le_sup_left) ⟨z,rfl⟩)
  let t : (fixedField J)ˣ →* B := (fixedTorus J hJ).codRestrict B
    (fun k => (show (fixedTorus J hJ).range ≤ B from le_sup_right) ⟨k,rfl⟩)
  let N := pResidual 2 B
  have ht (k : (fixedField J)ˣ) : t k ∈ N := by
    apply mem_pResidual_of_orderOf_coprime
    have hc : Nat.Coprime 2 (Nat.card (fixedField J)ˣ) := by
      rw [Nat.card_units]
      change Nat.Coprime 2 (Nat.card {x : E // J.conj x=x}-1)
      rw [hfixed]
      apply Nat.coprime_two_left.mpr
      have he := (Even.pow_of_ne_zero (by decide : Even (2:ℕ)) (show n≠0 by omega))
      rw [Nat.odd_iff]
      have hmod := Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp he)
      have hp := Nat.two_pow_pos n
      omega
    exact hc.of_dvd_right ((orderOf_map_dvd t k).trans (orderOf_dvd_natCard k))
  have hq : 2<2^n := (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)
  obtain ⟨k,hk⟩ := exists_fixed_unit J hfixed hq
  let c : E := ((fixedUnit J k : Eˣ) : E) * (J.conj ((fixedUnit J k : Eˣ) : E))⁻¹ ^ 2
  have hc : c-1 ≠ 0 := sub_ne_zero.mpr (fixed_weight J hk)
  have hr : f.range ≤ N := by
    apply EvenInner.range_le_of_first_surjective J hcard hfixed f N
    intro a
    let a₀ := a/(c-1)
    obtain ⟨b,hb⟩ := huppert_II_10_4_trace_surjective J (2^n) hcard hfixed
      (-(a₀*J.conj a₀)) (by rw [map_neg,map_mul,J.conj_involutive,mul_comm])
    let z : hermitianUnipotentCoord J := ⟨(a₀,b), by
      change b + J.conj b + a₀*J.conj a₀=0
      rw [hb,neg_add_cancel]⟩
    have hz' : z.val.1=a/(c-1) := rfl
    refine ⟨hermitianTorusAction J (fixedUnit J k) z * z⁻¹, ?_, ?_⟩
    · change (hermitianTorusAction J (fixedUnit J k) z).val.1 + -z.val.1=a
      rw [hermitianTorusAction_fst,mul_assoc,hz']
      change a/(c-1)*c + -(a/(c-1))=a
      field_simp
      ring
    · have hact : t k * f z * (t k)⁻¹=f (hermitianTorusAction J (fixedUnit J k) z) :=
        Subtype.ext (EvenInner.projective_torus_action J hJ _ z)
      have hh := (inferInstance : N.Normal).conj_mem (t k)⁻¹ (N.inv_mem (ht k)) (f z)
      have hm := N.mul_mem (ht k) hh
      have he : t k * (f z * (t k)⁻¹ * (f z)⁻¹) = f (hermitianTorusAction J (fixedUnit J k) z * z⁻¹) := by
        rw [map_mul,map_inv,←hact]
        group
      rwa [he] at hm
  apply (pResidual_eq_top_iff 2 B).mp
  apply top_unique
  intro b _
  have hle : B ≤ N.map B.subtype := sup_le
    (by rintro _ ⟨z,rfl⟩; exact ⟨f z,hr ⟨z,rfl⟩,rfl⟩)
    (by rintro _ ⟨k,rfl⟩; exact ⟨t k,ht k,rfl⟩)
  obtain ⟨b',hb',he⟩ := hle b.property
  exact (Subtype.ext he : b'=b) ▸ hb'

/-- The root and fixed-field torus have trivial pointwise automorphism fixer. -/
theorem rootFixedTorus_fixer
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card E=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ x ∈ rootFixedTorus J hJ, a x=x) : a=1 := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨z,hz⟩ := SylowPointwiseInner.fixing_root_eq_root_conj J hJ hn hcard hconj a
    (fun z => hfix _ ((show projectiveRoot J hJ ≤ rootFixedTorus J hJ from le_sup_left) ⟨z,rfl⟩))
  have hq : 2<2^n := (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)
  obtain ⟨k,hk⟩ := exists_fixed_unit J hf hq
  let u := fixedUnit J k
  have hu : (u:E) ≠ 1 := fixedUnit_ne_one J hk
  have hu2 : (u:E)^2 ≠ 1 := by
    intro he
    have hh := (sq_eq_one_iff).mp he
    rcases hh with hh | hh
    · exact hu hh
    · exact hu (hh.trans (CharTwo.neg_eq 1))
  have ht := hfix (fixedTorus J hJ k)
    ((show (fixedTorus J hJ).range ≤ rootFixedTorus J hJ from le_sup_right) ⟨k,rfl⟩)
  rw [hz] at ht
  have hc : hermitianTorusPSU J hJ u * hermitianUnipotentPSU J hJ z *
      (hermitianTorusPSU J hJ u)⁻¹=hermitianUnipotentPSU J hJ z := by
    apply mul_inv_eq_iff_eq_mul.mpr
    exact (mul_inv_eq_iff_eq_mul.mp ht).symm
  rw [EvenInner.projective_torus_action] at hc
  have he := EvenInner.root_injective J hJ hc
  have h1 := congrArg (fun z : hermitianUnipotentCoord J => z.val.1) he
  have h2 := congrArg (fun z : hermitianUnipotentCoord J => z.val.2) he
  rw [hermitianTorusAction_fst] at h1
  rw [hermitianTorusAction_snd] at h2
  have hfU : J.conj (u:E)=(u:E) := fixedUnit_conj J k
  rw [hfU] at h1 h2
  have hz1 : z.val.1=0 := by
    have hw : (u:E)*(u:E)⁻¹^2 ≠ 1 := by
      simpa only [fixedUnit_conj] using fixed_weight J hk
    have hh : z.val.1*((u:E)*(u:E)⁻¹^2-1)=0 := by
      linear_combination h1
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hw)
  have hz2 : z.val.2=0 := by
    have hw : (u:E)⁻¹*(u:E)⁻¹ ≠ 1 := by
      rw [←pow_two,inv_pow]
      exact inv_ne_one.mpr hu2
    have hh : z.val.2*((u:E)⁻¹*(u:E)⁻¹-1)=0 := by
      linear_combination h2
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hw)
  have hz0 : z=1 := Subtype.ext (Prod.ext hz1 hz2)
  simp only [hz,hz0,map_one]

end BenderSuzuki.MatrixGroups.HermitianForm.OrdinaryBorel
