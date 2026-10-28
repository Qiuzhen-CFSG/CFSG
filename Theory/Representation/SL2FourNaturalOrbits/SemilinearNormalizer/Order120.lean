module
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.AmbientAction
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FiveLines
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.LocalCore
/-!
# The order-120 extension of a natural SL₂(4) action

Every order-120 subgroup of ΓL₂(4) containing SL₂(4) contains a full
Sylow two-subgroup. Sylow conjugacy places the field involution in it;
the resulting subgroup contains the standard SL₂(4)-by-field group,
and equality follows from the common order.

A faithful action with a marked normal natural SL₂(4) subgroup lies in
its literal binary-linear normalizer. The proof retains every ambient
operator, then conjugates the same linear coordinates to the standard
order-120 model. SourceAction.FourCoordinates applies this to the
original HS dotted action.

Source: Aschbacher--Smith 14.3.23(2)(ii), p.1000, using 6.2.5.
-/

public section
open Subgroup
namespace Representation.SL2FourNatural.SemilinearNormalizer
noncomputable section
local instance : Finite Gamma := Nat.finite_of_card_ne_zero (by rw [gamma_card]; decide)

open scoped Pointwise in
theorem subgroup_order_oneTwenty (H : Subgroup Gamma)
    (hK : special.range≤H) (hH : Nat.card H=120) :
    ∃ g : Gamma, H.map (MulAut.conj g).toMonoidHom=specialFieldGamma := by
  have hf : fieldElement^2=1 := by
    apply natural_injective
    rw [map_pow,natural_fieldElement,map_one]
    rw [pow_two]
    exact LinearEquiv.ext frobeniusLinear_involutive
  have hpg : IsPGroup 2 (zpowers fieldElement) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one hf)
  obtain ⟨S,hS⟩ := hpg.exists_le_sylow
  let P : Sylow 2 H := default
  have hPc : Nat.card P=8 := by rw [P.card_eq_multiplicity,hH]; decide +kernel
  obtain ⟨Q,hQ⟩ := (P.isPGroup'.map H.subtype).exists_le_sylow
  have hPQ : (P : Subgroup H).map H.subtype=(Q : Subgroup Gamma) :=
    eq_of_le_of_card_ge hQ (by rw [card_map_of_injective H.subtype_injective,hPc,sylow_gamma_card])
  have hQH : (Q : Subgroup Gamma)≤H := hPQ ▸ map_subtype_le (P : Subgroup H)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Gamma S Q
  let H' := H.map (MulAut.conj g⁻¹).toMonoidHom
  have hKH : special.range≤H' := by
    have hn : special.range.map (MulAut.conj g⁻¹).toMonoidHom=special.range :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top (g⁻¹)))
    rw [←hn]
    exact map_mono hK
  have hfield : fieldElement∈H' := by
    have hq : g*fieldElement*g⁻¹∈(Q : Subgroup Gamma) := by
      rw [←hg,Sylow.coe_subgroup_smul]
      exact ⟨fieldElement,hS (mem_zpowers _),rfl⟩
    refine ⟨g*fieldElement*g⁻¹,hQH hq,?_⟩
    change g⁻¹*(g*fieldElement*g⁻¹)*(g⁻¹)⁻¹=fieldElement
    group
  have hle : specialFieldGamma≤H' := sup_le hKH (zpowers_le.mpr hfield)
  have hcard : Nat.card specialFieldGamma=120 := by
    rw [Nat.card_congr specialFieldGammaSymmetricFiveEquiv.toEquiv,Nat.card_perm,Nat.card_fin]
    decide
  have hh : H'=specialFieldGamma := (eq_of_le_of_card_ge hle (by
    dsimp [H']
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective,hH,hcard])).symm
  exact ⟨g⁻¹,hh⟩

variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]

omit [Finite D] in
theorem coordinates_of_order_oneTwenty (ρ : Representation (ZMod 2) D U)
    (hf : Function.Injective ρ) (hD : Nat.card D=120)
    (K : Subgroup D) [K.Normal] (e : K ≃* SL) (c : U ≃ₗ[ZMod 2] V)
    (he : ∀ k w, c (ρ k.val w)=action (e k) (c w)) :
    ∃ (E : D ≃* specialField) (C : U ≃ₗ[ZMod 2] V),
      ∀ a w, C (ρ a w)=(E a).val (C w) := by
  let t : D →* BinaryGL := {
    toFun a := c.symm.trans ((LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)).trans c)
    map_one' := by
      apply LinearEquiv.ext
      intro w
      change c (ρ 1 (c.symm w))=w
      simp
    map_mul' a b := by
      apply LinearEquiv.ext
      intro w
      change c (ρ (a*b) (c.symm w))=c (ρ a (c.symm (c (ρ b (c.symm w)))))
      rw [c.symm_apply_apply,map_mul,Module.End.mul_apply] }
  have ht (a : D) (w : U) : t a (c w)=c (ρ a w) := by
    change c (ρ a (c.symm (c w)))=c (ρ a w)
    rw [c.symm_apply_apply]
  have hti : Function.Injective t := by
    intro a b hab
    apply hf
    apply LinearMap.ext
    intro w
    apply c.injective
    rw [←ht,←ht,hab]
  have hmark (k : K) : t k.val=action (e k) := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨u,rfl⟩ := c.surjective w
    exact (ht k.val u).trans (he k u)
  have hmap : K.map t=action.range := by
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨e ⟨k,hk⟩,(hmark ⟨k,hk⟩).symm⟩
    · rintro ⟨k,rfl⟩
      exact ⟨(e.symm k).val,(e.symm k).property,by rw [hmark,e.apply_symm_apply]⟩
  have hnorm : t.range≤normalizer := by
    rintro _ ⟨a,rfl⟩
    change t a∈Subgroup.normalizer (action.range : Set BinaryGL)
    rw [←hmap]
    exact K.le_normalizer_map t (mem_map_of_mem t (le_normalizer_of_normal (mem_top a)))
  let b := t.codRestrict normalizer (fun a => hnorm ⟨a,rfl⟩)
  let f := normalizerEquiv.symm.toMonoidHom.comp b
  have hfi : Function.Injective f := normalizerEquiv.symm.injective.comp
    ((MonoidHom.injective_codRestrict t normalizer _).mpr hti)
  have hnat (a : D) : natural (f a)=t a := by
    change (normalizerEquiv (normalizerEquiv.symm (b a))).val=t a
    rw [normalizerEquiv.apply_symm_apply]
    rfl
  have hfm (k : K) : f k.val=special (e k) := by
    apply natural_injective
    rw [hnat,natural_special,hmark]
  have hKf : special.range≤f.range := by
    rw [←marked_ambient_action_map K e f hfm]
    exact map_le_range f K
  have hcard : Nat.card f.range=120 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,hD]
  obtain ⟨g,hg⟩ := subgroup_order_oneTwenty f.range hKf hcard
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Injective f' := (MulAut.conj g).injective.comp hfi
  have hr : f'.range=specialFieldGamma := by
    rw [MonoidHom.range_comp]
    exact hg
  let E := ((MonoidHom.ofInjective hf').trans (MulEquiv.subgroupCongr hr)).trans specialFieldEquiv
  let C := c.trans (natural g)
  refine ⟨E,C,?_⟩
  intro a w
  have hE : (E a).val=natural (f' a) := rfl
  have hconj : natural (f' a)*natural g=natural g*t a := by
    rw [←hnat,←map_mul,←map_mul]
    apply congrArg natural
    change (g*f a*g⁻¹)*g=g*f a
    group
  change natural g (c (ρ a w))=(E a).val (natural g (c w))
  rw [hE,←ht]
  exact (LinearEquiv.congr_fun hconj (c w)).symm
end
end Representation.SL2FourNatural.SemilinearNormalizer
