module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.Injective
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.LinearAlgebra.UnitaryCubicSplit
public import Theory.LinearAlgebra.UnitaryCubicConjugacy

/-!
# Completing the unitary-cover branch of the normal split-prime theorem

The outside cubic's implementer has a scalar cube. A cube root in the
coefficient field would give an orthonormal eigenbasis and a fixed elementary
nine in the actual component, contradicting the ambient three-rank bound.
The resulting cubic field gives the exact cyclic centralizer of order q²−q+1.

Every outside subgroup of order three has a generator in the original actor's
component coset. Its implementer has the same scalar cube, so special-unitary
conjugacy lifts through the original marked action to conjugacy under the
literal component. No irreducibility, centralizer, or fusion premise is added.

Source: Aschbacher–Smith A.3.18, printed pp.51–53. Complete assembles this
last row, and OddRankSource applies it to the Cartan extension of 4.3.6.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.GroupTheory Polynomial BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.EvenInner
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverSingerUnitary
private def centralizerEquiv {G F : Type*} [Group G] [Field F]
    (K : Subgroup G) [K.Normal] (a : G) (J : HermitianForm 3 F) (e : K ≃* J.specialSubgroup) (g : J.unitarySubgroup)
    (hmark : ∀ k : K, (e (MulAut.conjNormal a k)).val =
      g.val*(e k).val*g.val⁻¹) :
    ((centralizer ({a}:Set G)).comap K.subtype) ≃*
      ((centralizer ({g.val}:Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype) := by
  let C := (centralizer ({a}:Set G)).comap K.subtype
  let D := (centralizer ({g.val}:Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype
  have hm (k : K) : k∈C ↔ e k∈D := by
    change (k:G) ∈ centralizer ({a}:Set G) ↔ (e k).val ∈ centralizer ({g.val}:Set (GL (Fin 3) F))
    rw [mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
    constructor
    · intro h
      have he : (MulAut.conjNormal a : MulAut K) k=k :=
        Subtype.ext (mul_inv_eq_iff_eq_mul.mpr h.symm)
      have hh := hmark k
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    · intro h
      have he : (MulAut.conjNormal a : MulAut K) k=k := by
        apply e.injective
        apply J.specialSubgroup.subtype_injective
        exact (hmark k).trans (mul_inv_eq_iff_eq_mul.mpr h.symm)
      exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
  exact
    { toFun := fun c => ⟨e c.val,(hm _).mp c.property⟩
      invFun := fun d => ⟨e.symm d.val,(hm _).mpr (by simpa only [e.apply_symm_apply] using d.property)⟩
      left_inv c := Subtype.ext (e.symm_apply_apply _)
      right_inv d := Subtype.ext (e.apply_symm_apply _)
      map_mul' c d := Subtype.ext (e.map_mul _ _) }

private theorem fixed_card {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (q : ℕ)
    (hq : Chapter1.Section02.LocalModels.CoverParameter true q)
    (hcard : Nat.card F=q^2) (hconj : ∀ x, J.conj x=x^q) :
    Nat.card {x : F // J.conj x=x}=q := by
  rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,_⟩
  · exact FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  · let : Fact q.Prime := ⟨hp⟩
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj q 1 (by decide) (by simpa using hcard) (by simpa using hconj)

/-- The same outside cubic has a scalar cube with no root in the original
unitary coefficient field. The split case would supply a fixed elementary nine. -/
theorem nonsplit_marking {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (K : Subgroup G) [K.Normal] (a : G) (ha : orderOf a=3) (haK : a∉K)
    (hr : primeRank 3 G≤2) (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F=q^2) (hconj : ∀ x, J.conj x=x^q)
    (hfixed : Nat.card {x : F // J.conj x=x}=q) (hdiv : 3 ∣ q+1)
    (e : K ≃* J.specialSubgroup) (g : J.unitarySubgroup)
    (hmark : ∀ k : K, (e (MulAut.conjNormal a k)).val=g.val*(e k).val*g.val⁻¹) :
    ∃ z : Fˣ, g.val^3=GeneralLinearGroup.scalar (Fin 3) z ∧
      J.conj (z:F)*z=1 ∧ ∀ b : F, b^3≠(z:F) := by
  let α : MulAut K := MulAut.conjNormal a
  have ha3 : a^3=1 := by simpa only [ha] using pow_orderOf_eq_one a
  have hα : α^3=1 := by change (MulAut.conjNormal a : MulAut K)^3=1; rw [←map_pow,ha3,map_one]
  have hcomm (s : J.specialSubgroup) : Commute (g.val^3) s.val := by
    obtain ⟨k,rfl⟩ := e.surjective s
    have he := congrArg (fun b : MulAut K => (e (b k)).val) hα
    change (e (α (α (α k)))).val=(e k).val at he
    rw [hmark,hmark,hmark] at he
    have he' : g.val^3*(e k).val*(g.val^3)⁻¹=(e k).val := by
      convert he using 1
      simp only [pow_succ,pow_zero]
      group
    exact mul_inv_eq_iff_eq_mul.mp he'
  obtain ⟨z,hz⟩ := Matrix.UnitaryCubic.centralizer_scalar J q hcard hfixed hconj hdiv (g.val^3) hcomm
  have hzu : GeneralLinearGroup.scalar (Fin 3) z∈J.unitarySubgroup :=
    hz ▸ J.unitarySubgroup.pow_mem g.property 3
  have hzn : J.conj (z:F)*z=1 := congrArg Units.val ((Matrix.UnitaryCubic.scalar_unitary J z).mp hzu)
  let C := (centralizer ({a}:Set G)).comap K.subtype
  let D := (centralizer ({g.val}:Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype
  let E : C ≃* D := centralizerEquiv K a J e g hmark
  obtain ⟨w,hw⟩ := exists_prime_orderOf_dvd_card' (G := normOne J) 3
    (by rwa [normOne_card J hcard hconj])
  have hw' : IsPrimitiveRoot (w.val:F) 3 := by
    rw [IsPrimitiveRoot.iff_orderOf,orderOf_units]
    exact (orderOf_injective (normOne J).subtype (normOne J).subtype_injective w).trans hw
  refine ⟨z,hz,hzn,?_⟩
  intro b hb
  have hD := Matrix.UnitaryCubic.split_centralizer_rank J q hcard hconj hfixed hdiv g z hzn hz w.val b hw' hb
  have hC : 2≤primeRank 3 C := hD.trans
    (primeRank_le_of_injective 3 E.symm.toMonoidHom E.symm.injective)
  let j : C →* G := K.subtype.comp C.subtype
  have hj : Function.Injective j := K.subtype_injective.comp C.subtype_injective
  have hCeq : primeRank 3 C=2 := by
    have hh := (Theory.GroupTheory.primeRank_le_of_injective 3 j hj).trans hr
    omega
  obtain ⟨B,hB,hcardB⟩ := exists_elementaryAbelian_card_primeRank (G := C) (p := 3)
  let := hB
  let B' := B.map j
  let : IsElementaryAbelian 3 B' := IsElementaryAbelian.map j
  have hB'K : B'≤K := by rintro _ ⟨v,_,rfl⟩; exact v.val.property
  have hfix : B'≤centralizer ({a}:Set G) := by rintro _ ⟨v,_,rfl⟩; exact v.property
  have hcard' : Nat.card B'=3^2 := by rw [card_map_of_injective hj,hcardB,hCeq]
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join B' a ha
    (fun h => haK (hB'K h)) hfix hcard'
  omega

/-- The centralizer of the actual outside unitary-cover cubic is cyclic of
the exact source order q²−q+1, without an irreducibility premise. -/
theorem unitary_centralizer {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (a : G) (ha : orderOf a=3) (haK : a∉K)
    (hr : primeRank 3 G≤2) (q : ℕ)
    (hq : Chapter1.Section02.LocalModels.CoverParameter true q)
    (hmod : SignedCongruence true q)
    (hdiag : IsUnitaryDiagonal K q (MulAut.conjNormal a)) :
    IsCyclic ((centralizer ({a}:Set G)).comap K.subtype) ∧
      Nat.card ((centralizer ({a}:Set G)).comap K.subtype)=q^2-q+1 := by
  obtain ⟨F,_,_,J,hF,hconj,e,g,hmark⟩ := hdiag
  have hdiv : 3 ∣ q+1 := by
    change q%3=2 at hmod
    exact Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨z,hz,hzn,hnonsplit⟩ := nonsplit_marking K a ha haK hr J q hF hconj
    (fixed_card J q hq hF hconj) hdiv e g hmark
  have hm : IsCyclic ((centralizer ({g.val}:Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype) ∧
      Nat.card ((centralizer ({g.val}:Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype)=q^2-q+1 := by
    obtain ⟨p,n,hp,hn,rfl⟩ : ∃ p n : ℕ, p.Prime ∧ 0<n ∧ q=p^n := by
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,_⟩
      · exact ⟨2,n,Nat.prime_two,by omega,rfl⟩
      · exact ⟨q,1,hp,by decide,by simp⟩
    let : Fact p.Prime := ⟨hp⟩
    let : Fintype F := Fintype.ofFinite F
    let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := n*2) (by
      simpa only [←Nat.card_eq_fintype_card,pow_mul] using hF)
    exact Matrix.UnitarySinger.centralizer J hn hF hconj hdiv g z hzn (congrArg Units.val hz) hnonsplit
  let E := centralizerEquiv K a J e g hmark
  let := hm.1
  refine ⟨isCyclic_of_injective E.toMonoidHom E.injective,?_⟩
  rw [Nat.card_congr E.toEquiv,hm.2]

private theorem model_conjugate {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (q : ℕ)
    (hq : Chapter1.Section02.LocalModels.CoverParameter true q)
    (hcard : Nat.card F=q^2) (hconj : ∀ x, J.conj x=x^q) (hdiv : 3 ∣ q+1)
    (g h : J.unitarySubgroup) (z : Fˣ) (hz : J.conj (z:F)*z=1)
    (hg : g.val.val^3=Matrix.scalar (Fin 3) (z:F))
    (hh : h.val.val^3=Matrix.scalar (Fin 3) (z:F)) (hnonsplit : ∀ a : F, a^3≠(z:F)) :
    ∃ P : J.specialSubgroup, P.val*g.val*P.val⁻¹=h.val := by
  obtain ⟨p,n,hp,hn,rfl⟩ : ∃ p n : ℕ, p.Prime ∧ 0<n ∧ q=p^n := by
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,_⟩
    · exact ⟨2,n,Nat.prime_two,by omega,rfl⟩
    · exact ⟨q,1,hp,by decide,by simp⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := n*2) (by
    simpa only [←Nat.card_eq_fintype_card,pow_mul] using hcard)
  exact Matrix.UnitarySinger.special_conjugate_of_same_cube J hn hcard hconj hdiv g h z hz hg hh hnonsplit

private theorem coset_cubic_conjugate {G F : Type*} [Group G] [Field F] [Finite F]
    (K : Subgroup G) [K.Normal] (a : G) (ha : a^3=1)
    (J : HermitianForm 3 F) (q : ℕ)
    (hq : Chapter1.Section02.LocalModels.CoverParameter true q)
    (hcard : Nat.card F=q^2) (hconj : ∀ x, J.conj x=x^q) (hdiv : 3 ∣ q+1)
    (e : K ≃* J.specialSubgroup) (g : J.unitarySubgroup)
    (hmark : ∀ k : K, (e (MulAut.conjNormal a k)).val =
      g.val*(e k).val*g.val⁻¹)
    (z : Fˣ) (hz : g.val^3=GeneralLinearGroup.scalar (Fin 3) z)
    (hzn : J.conj (z:F)*z=1)
    (hn : ∀ b : F, b^3≠(z:F)) (k : K) (hk : ((k:G)*a)^3=1) :
    ∃ l : K, (l:G)*a*(l:G)⁻¹=(k:G)*a := by
  let α : MulAut K := MulAut.conjNormal a
  have hprod : k*α k*(MulAut.conjNormal (a^2) k)=1 := by
    apply K.subtype_injective
    change (k:G)*(a*(k:G)*a⁻¹)*(a^2*(k:G)*(a^2)⁻¹)=1
    calc
      _ = ((k:G)*a)^3*(a^3)⁻¹ := by
        simp only [pow_succ,pow_zero]
        group
      _ = 1 := by rw [hk,ha]; simp
  have hmark2 : (e (MulAut.conjNormal (a^2) k)).val=
      g.val^2*(e k).val*(g.val^2)⁻¹ := by
    have he : (MulAut.conjNormal (a^2) : MulAut K) k=α (α k) := by
      rw [map_pow,pow_two,MulAut.mul_apply]
    rw [he,hmark,hmark]
    simp only [pow_two]
    group
  let A := (e k).val
  have hprod' : A*(g.val*A*g.val⁻¹)*(g.val^2*A*(g.val^2)⁻¹)=1 := by
    have hh := congrArg (fun t : K => (e t).val) hprod
    simpa only [map_mul,map_one,Subgroup.coe_mul,Subgroup.coe_one,α,hmark,hmark2] using hh
  have hcube : (A*g.val)^3=g.val^3 := by
    calc
      _ = (A*(g.val*A*g.val⁻¹)*(g.val^2*A*(g.val^2)⁻¹))*g.val^3 := by
        simp only [pow_succ,pow_zero]
        group
      _ = g.val^3 := by rw [hprod',one_mul]
  let B : J.unitarySubgroup := ⟨A*g.val,
    J.unitarySubgroup.mul_mem (e k).property.1 g.property⟩
  obtain ⟨P,hP⟩ := model_conjugate J q hq hcard hconj hdiv g B z hzn
    (congrArg Units.val hz) (congrArg Units.val (hcube.trans hz)) hn
  let l := e.symm P
  have hl : l*(α l)⁻¹=k := by
    apply e.injective
    apply Subtype.ext
    simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,α,hmark,show e l=P from e.apply_symm_apply P]
    calc
      _ = P.val*g.val*(P.val)⁻¹*g.val⁻¹ := by group
      _ = A := by
        rw [hP]
        change (A*g.val)*g.val⁻¹=A
        group
  refine ⟨l,?_⟩
  have hh := congrArg (fun t : K => (t:G)*a) hl
  change ((l:G)*(a*(l:G)*a⁻¹)⁻¹)*a=(k:G)*a at hh
  convert hh using 1
  group

private theorem exists_coset_generator {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (a : G) (ha : orderOf a=3)
    (hgen : K ⊔ zpowers a=⊤) (X : Subgroup G) (hX : Nat.card X=3) (hXK : ¬ X≤K) :
    ∃ k : K, ((k:G)*a)^3=1 ∧ X=zpowers ((k:G)*a) := by
  classical
  have ha3 : a^3=1 := by simpa only [ha] using pow_orderOf_eq_one a
  obtain ⟨b,hbX,hbK⟩ := Set.not_subset.mp hXK
  have hb3 : b^3=1 := by
    have hh : (⟨b,hbX⟩ : X)^Nat.card X=1 := pow_card_eq_one'
    rw [hX] at hh
    exact congrArg Subtype.val hh
  have hgenerator (c : G) (hcX : c∈X) (hcK : c∉K) (hc3 : c^3=1) : X=zpowers c := by
    have hc1 : c≠1 := fun h => hcK (h ▸ K.one_mem)
    have hco : orderOf c=3 := orderOf_eq_prime hc3 hc1
    apply (eq_of_le_of_card_ge (zpowers_le.mpr hcX) ?_).symm
    rw [Nat.card_zpowers,hco,hX]
  obtain ⟨k,hk,v,hv,hkv⟩ := mem_sup_of_normal_left.mp (show b∈K ⊔ zpowers a by rw [hgen]; trivial)
  rw [mem_zpowers_iff_mem_range_orderOf,ha] at hv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  have hi' : i<3 := Finset.mem_range.mp hi
  interval_cases i
  · have he : k=b := by simpa using hkv
    exact (hbK (he ▸ hk)).elim
  · have he : k*a=b := by simpa using hkv
    refine ⟨⟨k,hk⟩,?_,?_⟩
    · simpa only [he] using hb3
    · simpa only [he] using hgenerator b hbX hbK hb3
  · let k' : K := MulAut.conjNormal a (⟨k,hk⟩ : K)⁻¹
    have haInv : (a^2)⁻¹=a := by
      apply inv_eq_of_mul_eq_one_right
      rw [←pow_succ,ha3]
    have he : (k':G)*a=b⁻¹ := by
      rw [←hkv,_root_.mul_inv_rev,haInv]
      change (a*k⁻¹*a⁻¹)*a=a*k⁻¹
      group
    have hbInv3 : (b⁻¹)^3=1 := by rw [inv_pow,hb3,inv_one]
    refine ⟨k',?_,?_⟩
    · simpa only [he] using hbInv3
    · simpa only [he] using hgenerator b⁻¹ (X.inv_mem hbX)
        (fun h => hbK (by simpa using K.inv_mem h)) hbInv3

/-- Every outside subgroup of order three is fused under the actual unitary
cover to the subgroup generated by the original actor. -/
theorem unitary_fusion {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (a : G) (ha : orderOf a=3) (haK : a∉K)
    (hr : primeRank 3 G≤2) (hgen : K ⊔ zpowers a=⊤) (q : ℕ)
    (hq : Chapter1.Section02.LocalModels.CoverParameter true q)
    (hmod : SignedCongruence true q)
    (hdiag : IsUnitaryDiagonal K q (MulAut.conjNormal a)) :
    ∀ X : Subgroup G, Nat.card X=3 → ¬ X≤K →
      ∃ l : K, X.map (MulAut.conj l.val).toMonoidHom=zpowers a := by
  obtain ⟨F,_,_,J,hF,hconj,e,g,hmark⟩ := hdiag
  have hdiv : 3 ∣ q+1 := by
    change q%3=2 at hmod
    exact Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨z,hz,hzn,hn⟩ := nonsplit_marking K a ha haK hr J q hF hconj
    (fixed_card J q hq hF hconj) hdiv e g hmark
  intro X hX hXK
  obtain ⟨k,hk,hXeq⟩ := exists_coset_generator K a ha hgen X hX hXK
  have ha3 : a^3=1 := by simpa only [ha] using pow_orderOf_eq_one a
  obtain ⟨l,hl⟩ := coset_cubic_conjugate K a ha3 J q hq hF hconj hdiv e g hmark z hz hzn hn k hk
  refine ⟨l⁻¹,?_⟩
  rw [hXeq,MonoidHom.map_zpowers]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,Subgroup.coe_inv,inv_inv]
  rw [←hl]
  group

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverSingerUnitary
