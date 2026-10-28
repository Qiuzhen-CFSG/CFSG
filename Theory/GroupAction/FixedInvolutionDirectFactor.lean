module
public import Theory.GroupAction.FixedModuloCentralLine
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.OmegaCenterProduct
/-!
# Actual fixed involutions in a central direct factor

A binary normalizer acts on the elementary omega center of R. Its quotient
by a centralized elementary direct factor V is nonzero, so orbit counting
gives a fixed nonzero coset. Decompose a central involution representing that
coset as v*c in the actual internal product V*C. The complementary factor
c remains an involution, central in R, with every actor commutator in V.
The complement C itself need not be invariant under the actor.

Source application: Aschbacher--Smith 4.2.13, printed p.612.
-/
public noncomputable section
open Subgroup Stellmacher
open scoped commutatorElement Pointwise IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A binary normalizer of a direct product with a central elementary factor
fixes modulo that factor an actual central involution of the complementary
factor. The complement need not be invariant under the normalizer. -/
theorem exists_central_involution_fixed_modulo_direct_factor
    (R V C Q : Subgroup G) (hR : IsPGroup 2 R) (hQ : IsPGroup 2 Q)
    (hV : IsElementaryAbelian 2 V) (hs : R = V ⊔ C)
    (hd : V ⊓ C = ⊥) (hc : V ≤ centralizer (C : Set G)) (hne : C ≠ ⊥)
    (hn : Q ≤ normalizer (R : Set G)) (hQV : Q ≤ centralizer (V : Set G)) :
    ∃ r ∈ C, orderOf r = 2 ∧ r ∈ centralizer (R : Set G) ∧
      ∀ q ∈ Q, ⁅r,q⁆ ∈ V := by
  let := hV
  have hVR : V ≤ R := hs ▸ le_sup_left
  have hCR : C ≤ R := hs ▸ le_sup_right
  have hVC : V ≤ centralizer (R : Set G) := by
    apply le_centralizer_iff.mp
    rw [hs]
    exact sup_le (fun v hv w hw => congrArg V.subtype
      (mul_comm (⟨w,hw⟩ : V) ⟨v,hv⟩))
      (le_centralizer_iff.mp hc)
  let Z := omegaOneCenterAmbient R
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian R
  have hVZ : V ≤ Z := by
    intro v hv
    exact (mem_omegaOneCenterAmbient_iff R v).mpr
      ⟨hVR hv,elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv,hVC hv⟩
  have hQZ : Q ≤ normalizer (Z : Set G) := by
    intro q hq
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (omegaOneCenterAmbient R).map (MulAut.conj q).toMonoidHom = _
    rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj q).injective]
    exact congrArg omegaOneCenterAmbient (mem_normalizer_iff_map_conj_eq.mp (hn hq))
  have hstrict : V < Z := by
    apply lt_of_le_of_ne hVZ
    intro he
    let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hne
    have hC := hR.to_le hCR
    let : Nontrivial (center C) := hC.center_nontrivial
    have hdc : 2 ∣ Nat.card (center C) :=
      (hC.to_subgroup (center C)).card_eq_or_dvd.resolve_left (by
        intro he
        let : Subsingleton (center C) := (Nat.card_eq_one_iff_unique.mp he).1
        exact not_subsingleton (center C) inferInstance)
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center C) 2 hdc
    have hzC : (z.val : G) ∈ centralizer (C : Set G) := by
      intro c hc
      exact congrArg C.subtype (mem_center_iff.mp z.property ⟨c,hc⟩)
    have hzV : (z.val : G) ∈ centralizer (V : Set G) :=
      le_centralizer_iff.mp hc z.val.property
    have hzR : (z.val : G) ∈ centralizer (R : Set G) := by
      apply mem_centralizer_iff.mpr
      have hh : R ≤ centralizer ({(z.val : G)} : Set G) := by
        rw [hs]
        exact sup_le (fun v hv => mem_centralizer_singleton_iff.mpr (hzV v hv))
          (fun c hc => mem_centralizer_singleton_iff.mpr (hzC c hc))
      intro r hr
      exact mem_centralizer_singleton_iff.mp (hh hr)
    have hz2 : (z.val : G)^2 = 1 := by
      have hh := pow_orderOf_eq_one z
      rw [hz] at hh
      exact congrArg (C.subtype.comp (center C).subtype) hh
    have hzZ : (z.val : G) ∈ Z := (mem_omegaOneCenterAmbient_iff R _).mpr
      ⟨hCR z.val.property,hz2,hzR⟩
    have hz1 : (z.val : G) = 1 :=
      (show (z.val : G) ∈ (⊥ : Subgroup G) from hd ▸ ⟨he.symm ▸ hzZ,z.val.property⟩)
    have hz1' : z = 1 := Subtype.ext (Subtype.ext hz1)
    rw [hz1',orderOf_one] at hz
    omega
  obtain ⟨u,hu,huV,huQ⟩ := Theory.GroupAction.exists_nonidentity_fixed_modulo Q Z V hQ hQZ hQV hstrict
  have huR := (mem_omegaOneCenterAmbient_iff R u).mp hu
  have hum : u ∈ (V : Set G) * (C : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right V C (hc.trans (centralizer_le_normalizer _))]
    exact hs ▸ huR.1
  obtain ⟨v,hv,c,hcC,hvu⟩ := hum
  change v*c=u at hvu
  have hcR : c ∈ centralizer (R : Set G) := by
    have hh : v⁻¹ * u ∈ centralizer (R : Set G) :=
      mul_mem (inv_mem (hVC hv)) huR.2.2
    rwa [←hvu,inv_mul_cancel_left] at hh
  have hc2 : c^2=1 := by
    have hh := huR.2.1
    rw [←hvu,(show Commute v c from (hc hv c hcC).symm).mul_pow,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv,one_mul] at hh
    exact hh
  have hcn : c ≠ 1 := by
    intro he
    apply huV
    rw [←hvu,he,mul_one]
    exact hv
  refine ⟨c,hcC,orderOf_eq_prime_iff.mpr ⟨hc2,hcn⟩,hcR,?_⟩
  intro q hq
  have hh := huQ q hq
  have hvq : Commute v q := (hQV hq v hv)
  have hvcq : Commute v ⁅c,q⁆ :=
    by
      have hvc : Commute v c := (hc hv c hcC).symm
      unfold commutatorElement
      exact ((hvc.mul_right hvq).mul_right hvc.inv_right).mul_right hvq.inv_right
  rw [←hvu,commutatorElement_mul_left_eq_conj_mul,hvq.commutator_eq,
    mul_one,hvcq.eq,mul_inv_cancel_right] at hh
  exact hh

end Subgroup
