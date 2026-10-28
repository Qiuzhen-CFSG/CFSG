module
public import Theory.Representation.RankOne.QuadraticRecognition.TwoRankOne
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryActors
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.Involution.Counting

/-!
# The small unitary quadratic actors and the uniform unitary bound

The actual PSU₃(2) has two-rank one. In a standard Hermitian basis, the
upper and lower central involutions generate a triple in the (0,2) block.
Conjugating the lower involution by the root (1,b), where b+conj(b)=1,
gives an involution with (1,0) entry one, outside that triple even modulo
scalars. The two-rank-one transvection obstruction gives the square bound.
An actual Hermitian basis change handles every form; odd-kernel involution
lifting and preservation of two-rank handle SU₃(2) without discarding its
scalar kernel. Combined with UnitaryActors, this covers every positive
binary field degree.

Source: DGS85, *Groups and Graphs*, Chapter 5 list on p.104 and (5.12),
pp.113–114; Hermitian coordinates are Huppert II.10.12. SourceTheorem and
CriticalRecognition apply the bounds to the full catalogue and the original
DGS critical quotient, respectively.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender BenderSuzuki.MatrixGroups
open BenderSuzuki.External Matrix
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
namespace Representation.RankOne.QuadraticRecognition
variable {F : Type*} [Field F] [Finite F]
private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem triple_lift {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (ho : Odd (Nat.card f.ker))
    (ht : ∃ t u x : H, IsInvolution t ∧ IsInvolution u ∧ IsInvolution x ∧
      t ≠ u ∧ x ≠ t ∧ x ≠ u ∧ x ≠ u⁻¹*t*u) :
    ∃ t u x : G, IsInvolution t ∧ IsInvolution u ∧ IsInvolution x ∧
      t ≠ u ∧ x ≠ t ∧ x ≠ u ∧ x ≠ u⁻¹*t*u := by
  obtain ⟨t,u,x,ht,hu,hx,htu,hxt,hxu,hxv⟩ := ht
  obtain ⟨a,ha,hat⟩ := Theory.GroupTheory.exists_involution_lift_of_odd_kernel f hf ho ht
  obtain ⟨b,hb,hbu⟩ := Theory.GroupTheory.exists_involution_lift_of_odd_kernel f hf ho hu
  obtain ⟨c,hc,hcx⟩ := Theory.GroupTheory.exists_involution_lift_of_odd_kernel f hf ho hx
  refine ⟨a,b,c,ha,hb,hc,?_,?_,?_,?_⟩
  · intro h; exact htu (hat.symm.trans ((congrArg f h).trans hbu))
  · intro h; exact hxt (hcx.symm.trans ((congrArg f h).trans hat))
  · intro h; exact hxu (hcx.symm.trans ((congrArg f h).trans hbu))
  · intro h
    apply hxv
    simpa only [map_mul,map_inv,hat,hbu,hcx] using congrArg f h

omit [Finite F] in
private theorem standard_projective_outside_triple [CharP F 2]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (b : F) (hb : b + J.conj b = 1) :
    ∃ t u x : ProjectiveSpecialUnitaryMatrixGroup J,
      IsInvolution t ∧ IsInvolution u ∧ IsInvolution x ∧
        t ≠ u ∧ x ≠ t ∧ x ≠ u ∧ x ≠ u⁻¹*t*u := by
  let z : hermitianUnipotentCoord J := ⟨(0,1),by simp [CharTwo.add_self_eq_zero]⟩
  let t := hermitianUnipotentSU J hJ z
  let w := hermitianWeylSU J hJ
  let u := w*t*w⁻¹
  let k := seed J hJ b hb
  let x := k*u*k⁻¹
  have htmat : t.val.val = !![1,0,1;0,1,0;0,0,1] := by
    simp [t,z,hermitianUnipotentSU,hermitianUnipotentGL,hermitianUnipotentMatrix]
  have hwmat : w.val.val = !![0,0,1;0,1,0;1,0,0] := by
    change (!![0,0,1;0,-1,0;1,0,0] : Matrix (Fin 3) (Fin 3) F) = _
    simp [CharTwo.neg_eq]
  have ht2 : t^2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    apply Units.ext
    change t.val.val*t.val.val = 1
    rw [htmat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three,CharTwo.add_self_eq_zero]
  have hw2 : w*w = 1 := by
    apply Subtype.ext
    apply Units.ext
    change w.val.val*w.val.val = 1
    rw [hwmat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three]
  have hwi : w⁻¹=w := inv_eq_of_mul_eq_one_left hw2
  have humat : u.val.val = !![1,0,0;0,1,0;1,0,1] := by
    change ((w*t*w⁻¹).val).val = _
    change (w.val.val*t.val.val)*w⁻¹.val.val = _
    rw [hwi,hwmat,htmat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three]
  have hu2 : u^2=1 := by
    change (MulAut.conj w t)^2=1
    rw [←map_pow,ht2,map_one]
  have hui : u⁻¹=u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu2)
  have hkmat : k.val.val = !![1,1,b;0,1,1;0,0,1] := seed_val J hJ b hb
  have hkimat : k⁻¹.val.val = !![1,1,b+1;0,1,1;0,0,1] := by
    have hm : k.val.val * !![1,1,b+1;0,1,1;0,0,1] = 1 := by
      rw [hkmat]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply,Fin.sum_univ_three,CharTwo.add_self_eq_zero,
          add_assoc]
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => k⁻¹.val.val*M) hm
    simpa only [←mul_assoc,show k⁻¹.val.val*k.val.val=1 from congrArg
      (fun g : J.specialSubgroup => g.val.val) (inv_mul_cancel k),one_mul,mul_one] using hh.symm
  have hx10 : x.val.val 1 0 = 1 := by
    change ((k.val.val*u.val.val)*k⁻¹.val.val) 1 0=1
    rw [hkmat,humat,hkimat]
    simp [Matrix.mul_apply,Fin.sum_univ_three]
  have hv10 : (u⁻¹*t*u).val.val 1 0 = 0 := by
    rw [hui]
    change ((u.val.val*t.val.val)*u.val.val) 1 0 = 0
    rw [humat,htmat]
    simp [Matrix.mul_apply,Fin.sum_univ_three]
  let q := J.specialToProjective
  have neq_of_entry (a c : J.specialSubgroup) (i j : Fin 3)
      (ha : a.val.val i j = 1) (hc : c.val.val i j = 0) : q a ≠ q c := by
    intro he
    have hp : ProjGenLinGroup.mk a.val = ProjGenLinGroup.mk c.val := by
      simpa only [q,J.specialToProjective_apply_val] using congrArg Subtype.val he
    obtain ⟨s,hs⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
    have hh := congrArg (fun M : GL (Fin 3) F => M.val i j) hs
    change (a.val.val * (GeneralLinearGroup.scalar (Fin 3) s).val) i j = _ at hh
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal,ha,hc] at hh
  have hqt : q t ≠ 1 := by
    rw [←q.map_one]
    apply neq_of_entry t 1 0 2
    · rw [htmat]; rfl
    · rfl
  have hqu : q u ≠ 1 := by
    change q (w*t*w⁻¹) ≠ 1
    rw [map_mul,map_mul,map_inv]
    intro he
    apply hqt
    exact (MulAut.conj (q w)).injective (he.trans (map_one _).symm)
  have hqx : q x ≠ 1 := by
    change q (k*u*k⁻¹) ≠ 1
    rw [map_mul,map_mul,map_inv]
    intro he
    exact hqu ((MulAut.conj (q k)).injective (he.trans (map_one _).symm))
  refine ⟨q t,q u,q x,⟨hqt,?_⟩,⟨hqu,?_⟩,⟨hqx,?_⟩,?_,?_,?_,?_⟩
  · rw [←map_pow,ht2,map_one]
  · rw [←map_pow,hu2,map_one]
  · have hx2 : x^2=1 := by
      change (MulAut.conj k u)^2=1
      rw [←map_pow,hu2,map_one]
    rw [←map_pow,hx2,map_one]
  · exact neq_of_entry t u 0 2 (by rw [htmat]; rfl) (by rw [humat]; rfl)
  · exact neq_of_entry x t 1 0 hx10 (by rw [htmat]; rfl)
  · exact neq_of_entry x u 1 0 hx10 (by rw [humat]; rfl)
  · rw [←map_inv,←map_mul,←map_mul]
    exact neq_of_entry x (u⁻¹*t*u) 1 0 hx10 hv10

private theorem projective_outside_triple (J : HermitianForm 3 F)
    (hcard : Nat.card F = 2^2) (hconj : ∀ x, J.conj x=x^2) :
    ∃ t u x : ProjectiveSpecialUnitaryMatrixGroup J,
      IsInvolution t ∧ IsInvolution u ∧ IsInvolution x ∧
        t ≠ u ∧ x ≠ t ∧ x ≠ u ∧ x ≠ u⁻¹*t*u := by
  have hc : Nat.card F = (2^1)^2 := by simpa using hcard
  let : CharP F 2 := charTwo_of_card hc
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 (by decide) hc
      (by simpa using hconj)
  obtain ⟨e⟩ := exists_projectiveEquiv J 2 hcard hfixed
  obtain ⟨b,hb⟩ := huppert_II_10_4_trace_surjective (standardForm J) 2 hcard hfixed 1 (by simp)
  apply triple_lift e.toMonoidHom e.surjective
  · rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective,card_bot]
    decide
  · exact standard_projective_outside_triple (standardForm J) rfl b hb

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- The PSU₃(2) endpoint of the quadratic square bound, on the actual model. -/
theorem psu3_two_quadratic_square_bound (J : HermitianForm 3 F)
    (hcard : Nat.card F = 2^2) (hconj : ∀ x, J.conj x=x^2)
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hf : Function.Injective ρ) (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hq : IsQuadratic ρ A) : Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  obtain ⟨t,u,x,ht,hu,hx,htu,hxt,hxu,hxv⟩ := projective_outside_triple J hcard hconj
  have hr : primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 1 :=
    (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide)
      (by simpa using hcard) (by simpa using hconj)).le
  exact square_bound_of_two_rank_one hr t u x ht hu hx htu hxt hxu hxv ρ hf A hq

/-- The faithful SU₃(2) endpoint retains its odd scalar kernel. -/
theorem su3_two_quadratic_square_bound (J : HermitianForm 3 F)
    (hcard : Nat.card F = 2^2) (hconj : ∀ x, J.conj x=x^2)
    (ρ : Representation (ZMod 2) J.specialSubgroup V)
    (hf : Function.Injective ρ) (A : Subgroup J.specialSubgroup)
    (hq : IsQuadratic ρ A) : Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  obtain ⟨t,u,x,ht,hu,hx,htu,hxt,hxu,hxv⟩ := triple_lift J.specialToProjective
    J.specialToProjective_surjective J.odd_card_specialToProjective_ker
    (projective_outside_triple J hcard hconj)
  have hr : primeRank 2 J.specialSubgroup ≤ 1 := by
    rw [primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide)
      (by simpa using hcard) (by simpa using hconj)).le
  exact square_bound_of_two_rank_one hr t u x ht hu hx htu hxt hxu hxv ρ hf A hq


/-- DGS unitary bounds for every positive field degree, including SU₃(2). -/
theorem su3_all_quadratic_bounds (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (hf : Function.Injective ρ)
    (hfix : fixedSpace ρ ⊤ = ⊥) (A : Subgroup J.specialSubgroup) (hq : IsQuadratic ρ A) :
    Nat.card A ≤ Nat.card (V ⧸ fixedSpace ρ A) ∧
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  by_cases hn2 : 2 ≤ n
  · exact su3_quadratic_bounds J hn2 hcard hconj ρ hf hfix A hq
  have hn1 : n = 1 := by omega
  have hb := su3_two_quadratic_square_bound J (by simpa only [hn1,pow_one] using hcard)
    (by simpa only [hn1,pow_one] using hconj) ρ hf A hq
  exact ⟨(Nat.le_self_pow (by decide) _).trans hb,hb⟩

/-- DGS unitary bounds for every positive field degree, including PSU₃(2). -/
theorem psu3_all_quadratic_bounds (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hf : Function.Injective ρ) (hfix : fixedSpace ρ ⊤ = ⊥)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hq : IsQuadratic ρ A) :
    Nat.card A ≤ Nat.card (V ⧸ fixedSpace ρ A) ∧
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  by_cases hn2 : 2 ≤ n
  · exact psu3_quadratic_bounds J hn2 hcard hconj ρ hf hfix A hq
  have hn1 : n = 1 := by omega
  have hb := psu3_two_quadratic_square_bound J (by simpa only [hn1,pow_one] using hcard)
    (by simpa only [hn1,pow_one] using hconj) ρ hf A hq
  exact ⟨(Nat.le_self_pow (by decide) _).trans hb,hb⟩

end Representation.RankOne.QuadraticRecognition
