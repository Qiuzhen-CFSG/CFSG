module
public import Theory.SpecificGroups.ExoticTwoGroup.LocalModel
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group

/-!
# Marked identification of the exotic two-group

Every presentation of the exotic group of order 256 is isomorphic to the
concrete iterated semidirect product, carrying each of its six generators
to the corresponding marked element.

We map each cyclic factor by powers. Compatibility with each action is
checked on the two acting generators and the generators of the normal
factor, giving two successive semidirect-product lifts. Generation makes
the resulting homomorphism surjective; the common order 256 makes it
bijective. This construction uses only the presentation relations.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4(c), p.386.
The cyclic-factor construction follows `C4SquareSignSwapPresentation`.
-/

namespace ExoticTwoGroup.LocalModel

private def cyclicHom {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (a : G) (ha : a ^ n = 1) : Multiplicative (ZMod n) →* G where
  toFun i := a ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change a ^ (i.toAdd + j.toAdd).val = a ^ i.toAdd.val * a ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ ha).symm

private def pairHom {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (a b : G) (ha : a ^ n = 1) (hb : b ^ n = 1) (hab : Commute a b) :
    (Multiplicative (ZMod n) × Multiplicative (ZMod n)) →* G where
  toFun x := cyclicHom a ha x.1 * cyclicHom b hb x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    have h : Commute (cyclicHom b hb x.2) (cyclicHom a ha y.1) :=
      hab.symm.pow_pow _ _
    calc
      _ = cyclicHom a ha x.1 *
        (cyclicHom a ha y.1 * cyclicHom b hb x.2) * cyclicHom b hb y.2 := by group
      _ = _ := by rw [h.eq.symm]; group

private theorem base_hom_ext {G : Type*} [Group G] (f g : Base →* G)
    (h₁ : f (Multiplicative.ofAdd 1, 1) = g (Multiplicative.ofAdd 1, 1))
    (h₂ : f (1, Multiplicative.ofAdd 1) = g (1, Multiplicative.ofAdd 1)) : f = g := by
  ext x
  have hx : x = (Multiplicative.ofAdd 1, 1) ^ x.1.toAdd.val *
      (1, Multiplicative.ofAdd 1) ^ x.2.toAdd.val :=
    (by decide : ∀ x : Base, x = (Multiplicative.ofAdd 1, 1) ^ x.1.toAdd.val *
      (1, Multiplicative.ofAdd 1) ^ x.2.toAdd.val) x
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [map_mul, map_pow, h₁, h₂]

private theorem actor_hom_ext {G : Type*} [Group G] (f g : Actor →* G)
    (h₁ : f (Multiplicative.ofAdd 1, 1) = g (Multiplicative.ofAdd 1, 1))
    (h₂ : f (1, Multiplicative.ofAdd 1) = g (1, Multiplicative.ofAdd 1)) : f = g := by
  ext x
  have hx : x = (Multiplicative.ofAdd 1, 1) ^ x.1.toAdd.val *
      (1, Multiplicative.ofAdd 1) ^ x.2.toAdd.val :=
    (by decide : ∀ x : Actor, x = (Multiplicative.ofAdd 1, 1) ^ x.1.toAdd.val *
      (1, Multiplicative.ofAdd 1) ^ x.2.toAdd.val) x
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [map_mul, map_pow, h₁, h₂]


private abbrev r₁ : Base := (Multiplicative.ofAdd 1, 1)
private abbrev r₂ : Base := (1, Multiplicative.ofAdd 1)
private abbrev s₁ : Actor := (Multiplicative.ofAdd 1, 1)
private abbrev s₂ : Actor := (1, Multiplicative.ofAdd 1)
private abbrev ca : Core := SemidirectProduct.inl r₁
private abbrev cb : Core := SemidirectProduct.inl r₂
private abbrev cg₁ : Core := SemidirectProduct.inr s₁
private abbrev cg₂ : Core := SemidirectProduct.inr s₂

private theorem actor_compatibility {N P : Type*} [Group N] [Group P]
    (φ : Actor →* MulAut N) (f : N →* P) (g : Actor →* P)
    (h₁ : f.comp (φ s₁).toMonoidHom = (MulAut.conj (g s₁)).toMonoidHom.comp f)
    (h₂ : f.comp (φ s₂).toMonoidHom = (MulAut.conj (g s₂)).toMonoidHom.comp f) :
    ∀ c, f.comp (φ c).toMonoidHom = (MulAut.conj (g c)).toMonoidHom.comp f := by
  have hm (c d : Actor)
      (hc : f.comp (φ c).toMonoidHom = (MulAut.conj (g c)).toMonoidHom.comp f)
      (hd : f.comp (φ d).toMonoidHom = (MulAut.conj (g d)).toMonoidHom.comp f) :
      f.comp (φ (c*d)).toMonoidHom =
        (MulAut.conj (g (c*d))).toMonoidHom.comp f := by
    have hc' := DFunLike.congr_fun hc
    have hd' := DFunLike.congr_fun hd
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc' hd'
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
      MulAut.mul_apply, MulAut.conj_apply, hc', hd']
    group
  intro c
  have hc : c = 1 ∨ c = s₁ ∨ c = s₂ ∨ c = s₁*s₂ :=
    (by decide : ∀ c : Actor, c = 1 ∨ c = s₁ ∨ c = s₂ ∨ c = s₁*s₂) c
  rcases hc with rfl | rfl | rfl | rfl
  · ext x; simp
  · exact h₁
  · exact h₂
  · exact hm s₁ s₂ h₁ h₂

variable {P : Type*} [Group P] (d : ExoticTwoGroup.Presentation P)

private abbrev baseHom : Base →* P := pairHom d.a d.b d.a_four d.b_four d.ab
private abbrev innerHom : Actor →* P := pairHom d.g₁ d.g₂ d.g₁_two d.g₂_two d.g₁g₂
private abbrev outerHom : Actor →* P := pairHom d.t d.z₀ d.t_two d.z₀_two d.tz₀

private theorem baseHom_r₁ : baseHom d r₁ = d.a := by
  simp [baseHom, pairHom, cyclicHom, r₁, show (1 : ZMod 4).val = 1 by decide]
private theorem baseHom_r₂ : baseHom d r₂ = d.b := by
  simp [baseHom, pairHom, cyclicHom, r₂, show (1 : ZMod 4).val = 1 by decide]
private theorem innerHom_s₁ : innerHom d s₁ = d.g₁ := by
  simp [innerHom, pairHom, cyclicHom, s₁, show (1 : ZMod 2).val = 1 by decide]
private theorem innerHom_s₂ : innerHom d s₂ = d.g₂ := by
  simp [innerHom, pairHom, cyclicHom, s₂, show (1 : ZMod 2).val = 1 by decide]
private theorem outerHom_s₁ : outerHom d s₁ = d.t := by
  simp [outerHom, pairHom, cyclicHom, s₁, show (1 : ZMod 2).val = 1 by decide]
private theorem outerHom_s₂ : outerHom d s₂ = d.z₀ := by
  simp [outerHom, pairHom, cyclicHom, s₂, show (1 : ZMod 2).val = 1 by decide]

private theorem inner_compatibility (c : Actor) :
    (baseHom d).comp (innerAction c).toMonoidHom =
      (MulAut.conj (innerHom d c)).toMonoidHom.comp (baseHom d) := by
  apply actor_compatibility
  · apply base_hom_ext
    · change baseHom d (innerAction s₁ r₁) = _
      rw [show innerAction s₁ r₁ = r₁⁻¹ by decide]
      simpa only [map_inv, map_pow, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, baseHom_r₁, innerHom_s₁, MulAut.conj_apply] using d.g₁_a.symm
    · change baseHom d (innerAction s₁ r₂) = _
      rw [show innerAction s₁ r₂ = r₁^2 * r₂⁻¹ by decide]
      simpa only [map_inv, map_pow, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, baseHom_r₁, baseHom_r₂, innerHom_s₁, MulAut.conj_apply] using d.g₁_b.symm
  · apply base_hom_ext
    · change baseHom d (innerAction s₂ r₁) = _
      rw [show innerAction s₂ r₁ = r₁⁻¹ * r₂^2 by decide]
      simpa only [map_inv, map_pow, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, baseHom_r₁, baseHom_r₂, innerHom_s₂, MulAut.conj_apply] using d.g₂_a.symm
    · change baseHom d (innerAction s₂ r₂) = _
      rw [show innerAction s₂ r₂ = r₂⁻¹ by decide]
      simpa only [map_inv, map_pow, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, baseHom_r₂, innerHom_s₂, MulAut.conj_apply] using d.g₂_b.symm

private def coreHom : Core →* P :=
  SemidirectProduct.lift (baseHom d) (innerHom d) (inner_compatibility d)

private theorem core_hom_ext (f g : Core →* P)
    (ha : f ca = g ca) (hb : f cb = g cb)
    (hg₁ : f cg₁ = g cg₁) (hg₂ : f cg₂ = g cg₂) : f = g := by
  apply SemidirectProduct.hom_ext
  · exact base_hom_ext _ _ ha hb
  · exact actor_hom_ext _ _ hg₁ hg₂

private theorem coreHom_ca : coreHom d ca = d.a := by
  simpa only [coreHom, SemidirectProduct.lift_inl] using baseHom_r₁ d
private theorem coreHom_cb : coreHom d cb = d.b := by
  simpa only [coreHom, SemidirectProduct.lift_inl] using baseHom_r₂ d
private theorem coreHom_cg₁ : coreHom d cg₁ = d.g₁ := by
  simpa only [coreHom, SemidirectProduct.lift_inr] using innerHom_s₁ d
private theorem coreHom_cg₂ : coreHom d cg₂ = d.g₂ := by
  simpa only [coreHom, SemidirectProduct.lift_inr] using innerHom_s₂ d

private theorem outer_compatibility (c : Actor) :
    (coreHom d).comp (outerAction c).toMonoidHom =
      (MulAut.conj (outerHom d c)).toMonoidHom.comp (coreHom d) := by
  apply actor_compatibility
  · apply core_hom_ext
    · change coreHom d (outerAction s₁ ca) = _
      rw [show outerAction s₁ ca = cb by decide +kernel]
      simpa only [map_inv, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        coreHom_ca, coreHom_cb, coreHom_cg₁, coreHom_cg₂,
        outerHom_s₁, MulAut.conj_apply] using d.t_a.symm
    · change coreHom d (outerAction s₁ cb) = _
      rw [show outerAction s₁ cb = ca by decide +kernel]
      simpa only [map_inv, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        coreHom_ca, coreHom_cb, coreHom_cg₁, coreHom_cg₂,
        outerHom_s₁, MulAut.conj_apply] using d.t_b.symm
    · change coreHom d (outerAction s₁ cg₁) = _
      rw [show outerAction s₁ cg₁ = cg₂ by decide +kernel]
      simpa only [map_inv, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        coreHom_ca, coreHom_cb, coreHom_cg₁, coreHom_cg₂,
        outerHom_s₁, MulAut.conj_apply] using d.t_g₁.symm
    · change coreHom d (outerAction s₁ cg₂) = _
      rw [show outerAction s₁ cg₂ = cg₁ by decide +kernel]
      simpa only [map_inv, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        coreHom_ca, coreHom_cb, coreHom_cg₁, coreHom_cg₂,
        outerHom_s₁, MulAut.conj_apply] using d.t_g₂.symm
  · apply core_hom_ext
    · change coreHom d (outerAction s₂ ca) = _
      rw [show outerAction s₂ ca = ca⁻¹ by decide +kernel]
      simpa only [map_inv, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        coreHom_ca, coreHom_cb, coreHom_cg₁, coreHom_cg₂,
        outerHom_s₂, MulAut.conj_apply] using d.z₀_a.symm
    · change coreHom d (outerAction s₂ cb) = _
      rw [show outerAction s₂ cb = cb⁻¹ by decide +kernel]
      simpa only [map_inv, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        coreHom_ca, coreHom_cb, coreHom_cg₁, coreHom_cg₂,
        outerHom_s₂, MulAut.conj_apply] using d.z₀_b.symm
    · change coreHom d (outerAction s₂ cg₁) = _
      rw [show outerAction s₂ cg₁ = ca * cg₁ by decide +kernel]
      simpa only [map_inv, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        coreHom_ca, coreHom_cb, coreHom_cg₁, coreHom_cg₂,
        outerHom_s₂, MulAut.conj_apply] using d.z₀_g₁.symm
    · change coreHom d (outerAction s₂ cg₂) = _
      rw [show outerAction s₂ cg₂ = cb * cg₂ by decide +kernel]
      simpa only [map_inv, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        coreHom_ca, coreHom_cb, coreHom_cg₁, coreHom_cg₂,
        outerHom_s₂, MulAut.conj_apply] using d.z₀_g₂.symm

/-- The homomorphism carrying the concrete generators to the marked presentation. -/
public def presentationHom : Model →* P :=
  SemidirectProduct.lift (coreHom d) (outerHom d) (outer_compatibility d)

public theorem presentationHom_a : presentationHom d a = d.a := by
  change presentationHom d (SemidirectProduct.inl ca) = _
  simpa only [presentationHom, SemidirectProduct.lift_inl] using coreHom_ca d

public theorem presentationHom_b : presentationHom d b = d.b := by
  change presentationHom d (SemidirectProduct.inl cb) = _
  simpa only [presentationHom, SemidirectProduct.lift_inl] using coreHom_cb d

public theorem presentationHom_g₁ : presentationHom d g₁ = d.g₁ := by
  change presentationHom d (SemidirectProduct.inl cg₁) = _
  simpa only [presentationHom, SemidirectProduct.lift_inl] using coreHom_cg₁ d

public theorem presentationHom_g₂ : presentationHom d g₂ = d.g₂ := by
  change presentationHom d (SemidirectProduct.inl cg₂) = _
  simpa only [presentationHom, SemidirectProduct.lift_inl] using coreHom_cg₂ d

public theorem presentationHom_t : presentationHom d t = d.t := by
  change presentationHom d (SemidirectProduct.inr s₁) = _
  simpa only [presentationHom, SemidirectProduct.lift_inr] using outerHom_s₁ d

public theorem presentationHom_z₀ : presentationHom d z₀ = d.z₀ := by
  change presentationHom d (SemidirectProduct.inr s₂) = _
  simpa only [presentationHom, SemidirectProduct.lift_inr] using outerHom_s₂ d

/-- Every marked exotic presentation is the concrete model, with all six generators fixed. -/
public theorem exists_marked_equiv [Finite P] :
    ∃ e : Model ≃* P, e a = d.a ∧ e b = d.b ∧ e g₁ = d.g₁ ∧
      e g₂ = d.g₂ ∧ e t = d.t ∧ e z₀ = d.z₀ := by
  let f := presentationHom d
  have hs : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← d.generate]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨a, presentationHom_a d⟩
    · exact ⟨b, presentationHom_b d⟩
    · exact ⟨g₁, presentationHom_g₁ d⟩
    · exact ⟨g₂, presentationHom_g₂ d⟩
    · exact ⟨t, presentationHom_t d⟩
    · exact ⟨z₀, presentationHom_z₀ d⟩
  let e := MulEquiv.ofBijective f (hs.bijective_of_nat_card_le (by
    rw [d.card, card_model]))
  exact ⟨e, presentationHom_a d, presentationHom_b d, presentationHom_g₁ d,
    presentationHom_g₂ d, presentationHom_t d, presentationHom_z₀ d⟩

end ExoticTwoGroup.LocalModel
