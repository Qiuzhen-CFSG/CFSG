module
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import Theory.Representation.BinaryConjugationCoordinates
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.Representation.NormalElementaryQuotient.ComponentModel
public import Theory.Representation.ElementaryPerfectSplit

/-!
# Reciprocal conjugate actions without FF offenders

For a faithful binary model with no FF offender, a noncentral elementary
actor has smaller centralizer index than the module it moves. Applying this
strict inequality to a conjugate module in both directions is impossible.
Thus reciprocal containment in a subgroup and its conjugate forces the two
modules to commute.

A component model suffices: a supplement to the full action centralizer
surjects onto the actual action image, and equality of the two quotient
kernels transports the non-FF property. The original H₀ application is in
Chapter13 Section04 FixedCoreSource/Nonsolvable/LinearReciprocal.
Source: Aschbacher–Smith 13.4.16, printed pp.912–913.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace BinaryConjugationCoordinates
variable {G Q M : Type*} [Group G] [Finite G] [Group Q]
  [AddCommGroup M] [Module (ZMod 2) M]

/-- A noncentral elementary actor of a non-FF model has strictly smaller
centralizer index than the module. Both indices are in the ambient group. -/
theorem centralizer_index_lt_of_nonFF
    (A U : Subgroup G) [IsElementaryAbelian 2 A]
    (hAU : A ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) Q M) (hσ : Function.Injective σ)
    (φ : A →* Q) (e : U ≃* Multiplicative M)
    (he : ∀ (a : A) (u : U),
      (e (U.normalizerMonoidHom ⟨a.val,hAU a.property⟩ u)).toAdd =
        σ (φ a) (e u).toAdd)
    (hn : ¬ IsFFModule σ) (hm : ¬ A ≤ centralizer (U : Set G)) :
    (centralizer (U : Set G)).relIndex A < (centralizer (A : Set G)).relIndex U := by
  let : Finite M := Finite.of_equiv U e.toEquiv
  let : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  let : IsElementaryAbelian 2 φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hne : φ.range ≠ ⊥ := by
    intro hb
    apply hm
    intro a ha
    have ha1 : φ ⟨a,ha⟩ = 1 := by
      have hh : φ ⟨a,ha⟩ ∈ φ.range := ⟨⟨a,ha⟩,rfl⟩
      rwa [hb,mem_bot] at hh
    exact (model_kernel A U hAU σ hσ φ e he).le ha1
  have hi : rank φ.range < fixedCodim σ φ.range :=
    lt_of_not_ge (fun hc => hn ⟨φ.range,⟨⟨hne,inferInstance⟩,hc⟩⟩)
  have hc : Nat.card φ.range = 2 ^ rank φ.range := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 φ.range).exists_card_eq
    rw [rank,hn,Nat.log_pow (by decide : 1 < 2)]
  have ha := model_card_range A U hAU σ hσ φ e he
  rw [inf_relIndex_left] at ha
  let j := U.subtype.comp e.symm.toMonoidHom
  have hj : j.range = U := by
    ext u
    constructor
    · rintro ⟨v,rfl⟩
      exact (e.symm v).property
    · intro hu
      exact ⟨e ⟨u,hu⟩,congrArg Subtype.val (e.symm_apply_apply _)⟩
  have hact (a : A) (v : M) : j (Multiplicative.ofAdd (σ (φ a) v)) =
      a.val * j (Multiplicative.ofAdd v) * a.val⁻¹ := by
    have hh := congrArg (fun w : M => (e.symm (Multiplicative.ofAdd w)).val)
      (he a (e.symm (Multiplicative.ofAdd v)))
    change (e.symm (e (U.normalizerMonoidHom ⟨a.val,hAU a.property⟩
      (e.symm (Multiplicative.ofAdd v))))).val =
      (e.symm (Multiplicative.ofAdd (σ (φ a) (e (e.symm (Multiplicative.ofAdd v))).toAdd))).val at hh
    rw [e.symm_apply_apply,e.apply_symm_apply] at hh
    exact hh.symm
  have hu := embedded_centralizer_index σ U A j
    (U.subtype_injective.comp e.symm.injective) hj φ hact
  rw [←ha,hc,hu]
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr hi

omit [Finite G] in
private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro a ha
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)

/-- Reciprocal containment in a group and its conjugate forces commuting
for a module whose actual faithful model has no FF offender. -/
theorem reciprocal_conjugate_commutator_eq_bot
    (H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) Q M) (hσ : Function.Injective σ)
    (φ : H →* Q) (e : U ≃* Multiplicative M)
    (he : ∀ (a : H) (u : U),
      (e (U.normalizerMonoidHom ⟨a.val,hHU a.property⟩ u)).toAdd =
        σ (φ a) (e u).toAdd)
    (hn : ¬ IsFFModule σ) (g : G)
    (h₁ : U.conjBy g ≤ H) (h₂ : U ≤ H.conjBy g) :
    ⁅U,U.conjBy g⁆ = ⊥ := by
  by_contra hm
  have hmove : ¬ U.conjBy g ≤ centralizer (U : Set G) := by
    intro hc
    exact hm (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hc)
  have hmove' : ¬ U.conjBy g⁻¹ ≤ centralizer (U : Set G) := by
    intro hc
    have hc' := map_mono (f := (MulAut.conj g).toMonoidHom) hc
    rw [centralizer_map_equiv] at hc'
    change (U.conjBy g⁻¹).conjBy g ≤ centralizer (U.conjBy g : Set G) at hc'
    rw [conjBy_inv'] at hc'
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr hc')
  have h₂' : U.conjBy g⁻¹ ≤ H := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h₂
    change U.conjBy g⁻¹ ≤ (H.conjBy g).conjBy g⁻¹ at hh
    rwa [conjBy_inv] at hh
  have step (k : G) (hk : U.conjBy k ≤ H)
      (hm : ¬ U.conjBy k ≤ centralizer (U : Set G)) :
      (centralizer (U : Set G)).relIndex (U.conjBy k) <
        (centralizer (U.conjBy k : Set G)).relIndex U := by
    let : IsElementaryAbelian 2 (U.conjBy k) := IsElementaryAbelian.map _
    exact centralizer_index_lt_of_nonFF (U.conjBy k) U (hk.trans hHU) σ hσ
      (φ.comp (inclusion hk)) e (fun a u => he (inclusion hk a) u) hn hm
  have hi := step g h₁ hmove
  have hj := step g⁻¹ h₂' hmove'
  have transport (A B : Subgroup G) :
      (centralizer (A.conjBy g : Set G)).relIndex (B.conjBy g) =
        (centralizer (A : Set G)).relIndex B := by
    change (centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
      (B.map (MulAut.conj g).toMonoidHom) = _
    rw [←centralizer_map_equiv A (MulAut.conj g)]
    exact relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have hx := transport U (U.conjBy g⁻¹)
  have hy := transport (U.conjBy g⁻¹) U
  rw [conjBy_inv'] at hx hy
  omega

/-- The same criterion for the literal conjugation image; no faithful
marking of the full ambient actor is required. -/
theorem reciprocal_conjugate_of_nonFF_image
    (H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G))
    (hn : ¬ IsFFModule (imageRepresentation (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hHU)))))
    (g : G) (h₁ : U.conjBy g ≤ H) (h₂ : U ≤ H.conjBy g) :
    ⁅U,U.conjBy g⁆ = ⊥ := by
  let ρ := elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion hHU))
  let e : U ≃* Multiplicative (Additive U) := {
    toFun u := Multiplicative.ofAdd (Additive.ofMul u)
    invFun v := v.toAdd.toMul
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact reciprocal_conjugate_commutator_eq_bot H U hHU (imageRepresentation ρ)
    (imageRepresentation_injective ρ) (actionHom ρ) e (fun _ _ => rfl) hn g h₁ h₂

omit [Finite G] in
/-- A centralizer supplement with the same literal kernel transfers the
non-FF obstruction from its model to the full conjugation image. -/
theorem nonFF_of_supplement_model
    (H U C : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G)) (hCH : C ≤ H)
    (hgen : C ⊔ (H ⊓ centralizer (U : Set G)) = H)
    (f : C →* Q) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (U : Set G)).subgroupOf C)
    (σ : Representation (ZMod 2) Q M)
    (E : Representation.Equiv (σ.comp f) (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion (hCH.trans hHU)))))
    (hn : ¬ IsFFModule σ) :
    ¬ IsFFModule (imageRepresentation (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hHU)))) := by
  let ρ := elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion hHU))
  let q := actionHom ρ
  let qC := q.comp (inclusion hCH)
  have hqker (a : H) : q a = 1 ↔ a.val ∈ centralizer (U : Set G) := by
    rw [actionHom_eq_one_iff]
    constructor
    · intro ha u hu
      have hh := congrArg (fun v : Additive U => v.toMul.val)
        (ha (Additive.ofMul ⟨u,hu⟩))
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro ha v
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr ((ha v.toMul.val v.toMul.property).symm)
  have hqC : Function.Surjective qC := by
    intro y
    obtain ⟨a,rfl⟩ := ρ.asGroupHom.rangeRestrict_surjective y
    have hN : C ≤ normalizer (H ⊓ centralizer (U : Set G) : Set G) :=
      (le_inf (hCH.trans H.le_normalizer)
        ((hCH.trans hHU).trans (normalizer_le_normalizer_centralizer U))).trans
          inf_normalizer_le_normalizer_inf
    have ha : a.val ∈ (C : Set G) * ((H ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right C _ hN,hgen]
      exact a.property
    obtain ⟨c,hc,n,hn,hcn⟩ := ha
    refine ⟨⟨c,hc⟩,?_⟩
    have he : (⟨c,hCH hc⟩ : H) * ⟨n,hn.1⟩ = a := Subtype.ext hcn
    change q ⟨c,hCH hc⟩ = q a
    rw [←he,map_mul,(hqker ⟨n,hn.1⟩).mpr hn.2,mul_one]
  have hker : qC.ker = f.ker := by
    rw [hk]
    ext c
    exact hqker (inclusion hCH c)
  exact nonFF_of_common_quotient f hf qC hqC hker σ (imageRepresentation ρ) E hn
end BinaryConjugationCoordinates
