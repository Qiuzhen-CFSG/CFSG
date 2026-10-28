module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryClassicalExclusion
public import Theory.SpecificGroups.SU3.OrdinaryBorelTransport
public import Theory.SpecificGroups.SU3.OrdinaryComponentRank

/-!
# The unitary fixed-field torus in the pure-line H1 case

The original fixed-field torus normalizes J(Q), hence the whole orbit W.
Its free action on a nonidentity element of the same marked inner sixteen
makes its action on W faithful. The pure-line stabilizer has image of
order dividing 24, while this odd torus has order at least fifteen.
Thus its order would divide three, a contradiction. The original
component Sylow, central quotient, and inner-action marking are retained.

This adapts the concrete fixed-torus calculation of
DoubledBinaryUnitaryExclusion to the S₄ pure-line image; it does not assert
that the component centralizes the paired plane.
Source: Aschbacher–Smith 7.7.3 H1 argument and 7.7.4, printed pp.704–706,
refs/quasithin.pdf, using the unitary calculation behind 15.1.21(iii).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureUnitary
open HermitianForm HermitianForm.BorelTorus HermitianForm.OrdinaryBorel
open HermitianForm.BorelTorus.EvenCenterAction

private theorem fixedTorus_free {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : x ∈ projectiveRoot J hJ) (hne : x ≠ 1)
    (k : (fixedField J)ˣ) (hc : Commute (fixedTorus J hJ k) x) : k = 1 := by
  by_contra hk
  obtain ⟨z,rfl⟩ := hx
  let u := fixedUnit J k
  have hu : (u : E) ≠ 1 := by
    intro he
    exact hk (Units.ext (Subtype.ext he))
  have hu2 : (u : E)^2 ≠ 1 := by
    intro he
    exact hu (CharTwo.sq_injective (by simpa using he))
  have hh := hc.mul_inv_cancel
  change hermitianTorusPSU J hJ u * hermitianUnipotentPSU J hJ z *
    (hermitianTorusPSU J hJ u)⁻¹ = hermitianUnipotentPSU J hJ z at hh
  rw [EvenInner.projective_torus_action] at hh
  have he := EvenInner.root_injective J hJ hh
  have h1 := congrArg (fun z : hermitianUnipotentCoord J => z.val.1) he
  have h2 := congrArg (fun z : hermitianUnipotentCoord J => z.val.2) he
  rw [hermitianTorusAction_fst] at h1
  rw [hermitianTorusAction_snd] at h2
  have hfU : J.conj (u:E) = (u:E) := k.val.property
  rw [hfU] at h1 h2
  have hz1 : z.val.1 = 0 := by
    have hw : (u:E)*(u:E)⁻¹^2 ≠ 1 := by
      have he : (u:E)*(u:E)⁻¹^2 = (u:E)⁻¹ := by field_simp
      rw [he]
      exact inv_ne_one.mpr hu
    have hh : z.val.1*((u:E)*(u:E)⁻¹^2-1)=0 := by linear_combination h1
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hw)
  have hz2 : z.val.2 = 0 := by
    have hw : (u:E)⁻¹*(u:E)⁻¹ ≠ 1 := by
      rw [←pow_two,inv_pow]
      exact inv_ne_one.mpr hu2
    have hh : z.val.2*((u:E)⁻¹*(u:E)⁻¹-1)=0 := by linear_combination h2
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hw)
  have hz : z = 1 := Subtype.ext (Prod.ext hz1 hz2)
  exact hne (by rw [hz,map_one])

private theorem inner_conj {K : Type*} [Group K] (k : K) :
    innerEquivCentralQuotient ((MulAut.conj : K →* MulAut K).rangeRestrict k) =
      (QuotientGroup.mk' (center K)) k := by
  change QuotientGroup.quotientMulEquivOfEq DoubleCoverCentralizer.conj_kernel
    ((QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k)) = _
  have he : (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k) = QuotientGroup.mk k := by
    apply (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [he]
  rfl

private theorem torus_bound
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    (W U K A : Subgroup G) (hAW : A ≤ W) (hKC : K ≤ centralizer (U : Set G))
    (hAN : A ≤ normalizer (K : Set G))
    (he : Nat.card (ChapterE.inducedAutomizer W (centralizer (U : Set G))) ∣ 24)
    (j : A →* K ⧸ center K)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a))
    (b : X →* K) (hBW : b.range.map K.subtype ≤ normalizer (W : Set G))
    (a : A) (hfree : ∀ x : X, Commute (j a) (QuotientGroup.mk' (center K) (b x)) → x = 1) :
    Nat.card X ∣ 24 := by
  let f : X →* normalizer (W : Set G) := (K.subtype.comp b).codRestrict _
    (fun x => hBW (mem_map_of_mem K.subtype (show b x ∈ b.range from ⟨x,rfl⟩)))
  let r₀ := W.normalizerMonoidHom.rangeRestrict.comp f
  let r : X →* ChapterE.inducedAutomizer W (centralizer (U : Set G)) :=
    r₀.codRestrict _ (fun x => ⟨f x,hKC (b x).property,rfl⟩)
  have hr : r.ker = ⊥ := by
    apply bot_unique
    intro x hx
    have hxW : ((b x : K) : G) ∈ centralizer (W : Set G) := by
      have hh : W.normalizerMonoidHom (f x) = 1 :=
        congrArg (fun y : ChapterE.inducedAutomizer W (centralizer (U : Set G)) => y.val.val) hx
      change f x ∈ W.normalizerMonoidHom.ker at hh
      rw [normalizerMonoidHom_ker] at hh
      exact hh
    apply hfree
    let e := innerEquivCentralQuotient (H := K)
    have hf : (e.symm (j a) : MulAut K) (b x) = b x := by
      rw [hact a]
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hxW a (hAW a.property))
    have hq : e.symm (QuotientGroup.mk' (center K) (b x)) =
        (MulAut.conj : K →* MulAut K).rangeRestrict (b x) := by
      apply e.injective
      rw [e.apply_symm_apply,inner_conj]
    apply e.symm.injective
    rw [map_mul,map_mul,hq]
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    change (e.symm (j a) : MulAut K) (b x * y * (b x)⁻¹) =
      b x * (e.symm (j a) : MulAut K) y * (b x)⁻¹
    rw [map_mul,map_mul,map_inv,hf]
  have hc := Nat.card_congr (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff r).mp hr)).toEquiv
  rw [hc]
  exact r.range.card_subgroup_dvd_card.trans he

private def wholeEquiv {K S : Type*} [Group K] [Group S]
    (hz : center K = ⊥) (e : K ⧸ center K ≃* S) : K ≃* S :=
  QuotientGroup.quotientBot.symm.trans ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)

/-- The fixed-field torus contradicts the literal pure-line S₄ action.
The original component Sylow is in Q, and Q normalizes the actual component;
neither placement is inferred from the abstract moving sixteen. -/
theorem unitary_exclusion
    {G : Type*} [Group G] [Finite G]
    (W U K A Q : Subgroup G) (hAW : A ≤ W) (hKC : K ≤ centralizer (U : Set G))
    (hAN : A ≤ normalizer (K : Set G)) (hz : center K = ⊥)
    (hp : IsPGroup 2 Q) (hQN : Q ≤ normalizer (K : Set G))
    (hNJ : normalizer (elementaryAbelianMaxJ Q : Set G) ≤ normalizer (W : Set G))
    (he : Nat.card (ChapterE.inducedAutomizer W (centralizer (U : Set G))) ∣ 24)
    (j : A →* K ⧸ center K) (hj : Nat.card j.range = 16)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a))
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ Q)
    (hAP : j.range ≤ (P.mapSurjective (QuotientGroup.mk'_surjective (center K)) : Subgroup _))
    {n : ℕ} (hn : 4 ≤ n) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2^n)) : False := by
  obtain ⟨F,_,_,J,hF,hconj,⟨em⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hF)
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
  obtain ⟨eJ⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hF hf
  let J₀ := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  have hJ₀ : J₀.form = !![0,0,1;0,1,0;1,0,0] := rfl
  have hf₀ : Nat.card {x : F // J₀.conj x=x}=2^n := hf
  have hc₀ : ∀ x, J₀.conj x=x^(2^n) := hconj
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    BenderSuzuki.External.huppert_II_10_13 J₀ (2^n)
      ((by decide : 2<2^4).trans_le (Nat.pow_le_pow_right (by decide) hn)) hF hf₀
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_surjective J₀.specialToProjective J₀.specialToProjective_surjective
  let e₀ := wholeEquiv hz (em.trans eJ)
  let R := P.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  let S := EvenTwoRank.rootSylow J₀ hJ₀ (by omega : 0<n) hF hf₀
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J₀) R S
  let e := e₀.trans (MulAut.conj g)
  let em' := (em.trans eJ).trans (MulAut.conj g)
  have heq (k : K) : em' (QuotientGroup.mk' (center K) k) = e k := rfl
  have hroot : (P : Subgroup K).map e.toMonoidHom = projectiveRoot J₀ hJ₀ := by
    change (P : Subgroup K).map ((MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom)=_
    rw [←map_map]
    exact congrArg Sylow.toSubgroup hg
  have hQP : Q.subgroupOf K = (P : Subgroup K) := by
    apply P.is_maximal' hp.comap_subtype
    intro k hk
    exact hPQ (mem_map_of_mem K.subtype hk)
  let b : (fixedField J₀)ˣ →* K := e.symm.toMonoidHom.comp (fixedTorus J₀ hJ₀)
  have hBW : b.range.map K.subtype ≤ normalizer (W : Set G) := by
    apply le_trans _ hNJ
    apply le_trans _ (rootFixedTorus_normalizes_thompson J₀ hJ₀ (by omega) hF hc₀ K Q hQN e
      (by rw [hQP,hroot]))
    rintro _ ⟨k,⟨x,rfl⟩,rfl⟩
    exact mem_map_of_mem K.subtype (mem_map_of_mem e.symm.toMonoidHom
      (mem_sup_right (show fixedTorus J₀ hJ₀ x ∈ (fixedTorus J₀ hJ₀).range from ⟨x,rfl⟩)))
  have hAn : j.range ≠ ⊥ := by intro hbot; rw [hbot,card_bot] at hj; omega
  obtain ⟨a,ha,hane⟩ := j.range.bot_or_exists_ne_one.resolve_left hAn
  obtain ⟨a,rfl⟩ := ha
  have haRoot : em' (j a) ∈ projectiveRoot J₀ hJ₀ := by
    obtain ⟨k,hk,hkj⟩ := hAP (show j a ∈ j.range from ⟨a,rfl⟩)
    rw [←hkj,heq,←hroot]
    exact mem_map_of_mem e.toMonoidHom hk
  have haNe : em' (j a) ≠ 1 := fun hh => hane (em'.injective (hh.trans (map_one em').symm))
  have hbound := torus_bound W U K A hAW hKC hAN he j hact b hBW a (by
    intro x hx
    have hh := hx.map em'.toMonoidHom
    change Commute (em' (j a)) (em' (QuotientGroup.mk' (center K) (b x))) at hh
    rw [heq] at hh
    have hb : e (b x) = fixedTorus J₀ hJ₀ x := e.apply_symm_apply _
    rw [hb] at hh
    exact fixedTorus_free J₀ hJ₀ _ haRoot haNe x hh.symm)
  rw [Nat.card_units] at hbound
  change Nat.card {x : F // J₀.conj x=x} - 1 ∣ 24 at hbound
  rw [hf₀] at hbound
  have hbig : 16 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
  have heven : Even (2^n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have ho : Odd (2^n-1) := by
    obtain ⟨k,hk⟩ := heven
    exact ⟨k-1,by omega⟩
  have hc : (2^n-1).Coprime 8 := by simpa using ho.coprime_two_right.pow_right 3
  have hd : 2^n-1 ∣ 3 := hc.dvd_of_dvd_mul_left hbound
  have hsmall := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureUnitary
