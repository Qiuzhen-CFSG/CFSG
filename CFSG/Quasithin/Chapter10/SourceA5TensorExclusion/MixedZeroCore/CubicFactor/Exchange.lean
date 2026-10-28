module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.CubicFactor.Reduction

/-!
# Factor exchange is nonscalar on the original Cartan quotient

Choose a nontrivial Cartan element supported on the first factor of the
original A₅×A₅ quotient. An element t outside N_G(L) sends its quotient
image to the second factor. If conjugation by t were a scalar power on
A modulo O₂(A∨T), the difference would lie in that two-core. Its image
in the original product is a nontrivial element of order three, impossible
for the image of a two-element.

This proves the exchange obstruction directly from the original marked
product quotient, without assuming a normalizer description or a field–swap
lift. It applies to every natural-number scalar power, in particular the
two powers associated with equal signs of the cubic characters.
Source: Aschbacher–Smith, original 9.3.1, printed p.732 of refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- Every tensor-factor exchange acts nonscalarly on the actual quotient torus. -/
theorem cartan_exchange_not_scalar (A : Subgroup G)
    (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (t : T) (htn : (t : G) ∉ normalizer (L : Set G)) (n : ℕ) :
    ¬ ∀ a : A,
      QuotientGroup.mk' (pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_right t * inclusion le_sup_left a * (inclusion le_sup_right t)⁻¹) =
      QuotientGroup.mk' (pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G))
        ((inclusion le_sup_left a)^n) := by
  intro hscalar
  let R := localOrbit T L
  let P := A ⊔ (T : Subgroup G)
  have hAR : A ≤ R := hAB.trans ((map_subtype_le _).trans inf_le_left)
  have hLR : L ≤ R := le_componentOrbit L T
  obtain ⟨q,hq,hk,hfirst,hsecond⟩ := source_a5_original_product_quotient D e
    m.sylow_not_normalizes_component t.property htn
  let qA := q.comp (inclusion hAR)
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 2) hA9
  have hi : Function.Injective qA :=
    (Theory.AlternatingFive.injective_on_three_subgroup q (hk ▸ pCore_isPGroup)
      (A.subgroupOf R) hAp.comap_subtype).comp (subgroupOfEquivOfLe hAR).symm.injective
  let axis := ((MonoidHom.snd _ _).comp qA).ker
  have hcaxis : Nat.card axis = 3 :=
    (Theory.AlternatingFive.nine_torus_coordinate_kernels qA hi hAp hA9).2.1
  have haxis : axis ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcaxis
    omega
  obtain ⟨a,hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp haxis
  let c := (qA a).1
  have hc2 : (qA a).2 = 1 := a.property
  have hc1 : c ≠ 1 := by
    intro he
    apply hane
    apply Subtype.ext
    apply hi
    change qA (a : A) = qA 1
    rw [map_one]
    exact Prod.ext he hc2
  have hc3 : c^3=1 := by
    have ha3 : a^3=1 := by simpa only [hcaxis] using (pow_card_eq_one' (x := a))
    have hh := congrArg (fun x : axis => (qA x).1) ha3
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,map_pow,map_one,Prod.pow_fst,Prod.fst_one] using hh
  obtain ⟨l,hl⟩ := e.surjective c
  obtain ⟨l,hl'⟩ := QuotientGroup.mk'_surjective (pCore 2 L) l
  have hlc : e (QuotientGroup.mk' (pCore 2 L) l) = c := hl' ▸ hl
  let aR : R := inclusion hAR (a : A)
  let lR : R := inclusion hLR l
  let τ : MulAut R := R.normalizerMonoidHom
    ⟨t,le_normalizer_componentOrbit L T t.property⟩
  have hqa : q aR = (c,1) := Prod.ext rfl hc2
  have hql : q lR = (c,1) := (hfirst l).trans (by rw [hlc])
  have hd : aR*lR⁻¹ ∈ pCore 2 R := by
    rw [←hk,MonoidHom.mem_ker,map_mul,map_inv,hqa,hql,mul_inv_cancel]
  have hτd : τ (aR*lR⁻¹) ∈ pCore 2 R := by
    have he := (pCore 2 R).characteristic_iff_map_eq.mp inferInstance τ
    exact he ▸ mem_map_of_mem τ.toMonoidHom hd
  have hτeq : q (τ aR) = q (τ lR) := by
    apply mul_inv_eq_one.mp
    have hh : q (τ (aR*lR⁻¹)) = 1 := by
      change τ (aR*lR⁻¹) ∈ q.ker
      rwa [hk]
    simpa only [map_mul,map_inv] using hh
  have hτl : q (τ lR) = (1,c) := (hsecond l).trans (by rw [hlc])
  let aP : P := inclusion le_sup_left (a : A)
  let tP : P := inclusion le_sup_right t
  let rP := tP*aP*tP⁻¹*(aP^n)⁻¹
  have hrP : rP ∈ pCore 2 P := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 P) (tP*aP*tP⁻¹*(aP^n)⁻¹) = 1
    rw [map_mul,map_inv,hscalar (a : A),mul_inv_cancel]
  let rR := τ aR*(aR^n)⁻¹
  have hr : (rR : G) = (rP : G) := rfl
  have hqr : q rR = ((c^n)⁻¹,c) := by
    change q (τ aR*(aR^n)⁻¹) = _
    rw [map_mul,map_inv,map_pow,hτeq,hτl,hqa]
    simp only [Prod.pow_mk,Prod.inv_mk,Prod.mk_mul_mk,one_pow,inv_one,one_mul,mul_one]
  have hthree : (q rR)^3=1 := by
    rw [hqr]
    apply Prod.ext
    · change ((c^n)⁻¹)^3=1
      rw [inv_pow,←pow_mul,Nat.mul_comm n 3,pow_mul,hc3,one_pow,inv_one]
    · exact hc3
  obtain ⟨k,hktwo⟩ := (pCore_isPGroup (p := 2) (G := P)) ⟨rP,hrP⟩
  have hrtwo : rR^(2^k)=1 := by
    apply Subtype.ext
    change (rR : G)^(2^k)=1
    rw [hr]
    exact congrArg (fun x : pCore 2 P => ((x : P) : G)) hktwo
  have htwo : (q rR)^(2^k)=1 := by rw [←map_pow,hrtwo,map_one]
  have hone : q rR = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow_left k)
      (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hthree))
  exact hc1 (congrArg Prod.snd (hqr.symm.trans hone))

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
