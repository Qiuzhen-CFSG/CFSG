module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.CubicRestriction
public import Theory.Representation.BinaryCubicPairs.FourSpace

/-!
# Noncommuting cubic actors have at most three-dimensional total support

The two moved planes span a space of dimension at most four. On a
four-dimensional span, the subgroup acting trivially on its quotient acts
faithfully by the original involution bound. Restriction preserves cubic
displacement ranges. The checked four-dimensional pair theorem therefore
produces an ambient involution of fixed codimension at most two, contradicting
the original bound. The sum of the moved planes has dimension at most three.

This supplies the global pair geometry missing from the maximal-intersection
construction in Aschbacher--Smith E.6.24, printed p.255. It does not assume
fixed-space TI or a factor decomposition.
-/

public section
open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

omit [Finite A] in
theorem Input.pair_moved_finrank_le_three (h : Input ρ C) (hC3 : Nat.card C = 3)
    (a : A)
    (hnc : ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) :
    finrank (ZMod 2) ↥(displacementSpan ρ C ⊤ ⊔
      displacementSpan ρ (C.map (MulAut.conj a).toMonoidHom) ⊤) ≤ 3 := by
  classical
  let D := C.map (MulAut.conj a).toMonoidHom
  let S := displacementSpan ρ C ⊤
  let R := displacementSpan ρ D ⊤
  let T := S ⊔ R
  have hS : finrank (ZMod 2) S = 2 := h.moved_finrank_eq_two_of_card_three hC3
  have hR : finrank (ZMod 2) R = 2 := by
    have he := displacementSpan_conjugate ρ C ⊤ a
    rw [map_top_action] at he
    change finrank (ZMod 2) (displacementSpan ρ (C.map (MulAut.conj a).toMonoidHom) ⊤) = 2
    rw [he, ← (Submodule.equivMapOfInjective (ρ a) (ρ.apply_bijective a).injective
      (displacementSpan ρ C ⊤)).finrank_eq]
    exact hS
  change finrank (ZMod 2) T ≤ 3
  by_contra hdim
  have hT : finrank (ZMod 2) T = 4 := by
    have he := S.finrank_sup_add_finrank_inf_eq R
    change finrank (ZMod 2) T + _ = _ at he
    omega
  push Not at hnc
  obtain ⟨c, hc, d, hd, hcd⟩ := hnc
  have hc1 : c ≠ 1 := by intro he; subst c; exact hcd (Commute.one_left d)
  have hd1 : d ≠ 1 := by intro he; subst d; exact hcd (Commute.one_right c)
  have hD3 : Nat.card D = 3 :=
    (Subgroup.card_map_of_injective (MulAut.conj a).injective).trans hC3
  have hc3 : c ^ 3 = 1 := by
    have hh : (⟨c, hc⟩ : C) ^ Nat.card C = 1 := pow_card_eq_one'
    rw [hC3] at hh
    exact congrArg Subtype.val hh
  have hd3 : d ^ 3 = 1 := by
    have hh : (⟨d, hd⟩ : D) ^ Nat.card D = 1 := pow_card_eq_one'
    rw [hD3] at hh
    exact congrArg Subtype.val hh
  have hcL : c ∈ quotientFixer ρ T := by
    intro v
    exact (show S ≤ T from le_sup_left) (Submodule.subset_span ⟨c, hc, v, Submodule.mem_top, rfl⟩)
  have hdL : d ∈ quotientFixer ρ T := by
    intro v
    exact (show R ≤ T from le_sup_right) (Submodule.subset_span ⟨d, hd, v, Submodule.mem_top, rfl⟩)
  let c' : quotientFixer ρ T := ⟨c, hcL⟩
  let d' : quotientFixer ρ T := ⟨d, hdL⟩
  have hc3' : c' ^ 3 = 1 := Subtype.ext hc3
  have hd3' : d' ^ 3 = 1 := Subtype.ext hd3
  let σ := onQuotientFixer ρ T
  have hσ : Function.Injective σ := h.onQuotientFixer_faithful T le_sup_left (by rw [hT, hS])
  have hcrange : ((σ c' - LinearMap.id).range).map T.subtype = S := by
    rw [cubic_range_onQuotientFixer T c' hc3']
    exact h.displacement_range_eq hc hc1
  have hdrange : ((σ d' - LinearMap.id).range).map T.subtype = R := by
    rw [cubic_range_onQuotientFixer T d' hd3']
    exact h.displacement_range_eq_conjugate a hd hd1
  have hcσ : finrank (ZMod 2) (σ c' - LinearMap.id).range = 2 := by
    rw [(Submodule.equivMapOfInjective T.subtype Subtype.val_injective _).finrank_eq, hcrange]
    exact hS
  have hdσ : finrank (ZMod 2) (σ d' - LinearMap.id).range = 2 := by
    rw [(Submodule.equivMapOfInjective T.subtype Subtype.val_injective _).finrank_eq, hdrange]
    exact hR
  have hfull : (σ c' - LinearMap.id).range ⊔ (σ d' - LinearMap.id).range = ⊤ := by
    apply Submodule.map_injective_of_injective (f := T.subtype) Subtype.val_injective
    rw [Submodule.map_sup, hcrange, hdrange, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨t, ht, hsmall⟩ := BinaryCubicPairs.exists_involution_of_four_space
    (ρ.comp (quotientFixer ρ T).subtype) σ hσ hT T.subtype Subtype.val_injective
    (fun _ _ => rfl) (fun g v => ⟨⟨ρ (g : A) v - v, g.property v⟩, rfl⟩)
    c' d' hc3' hd3' hcσ hdσ hfull
    (fun he => hcd (he.map (quotientFixer ρ T).subtype))
  have htA : orderOf (t : A) = 2 :=
    (orderOf_injective (quotientFixer ρ T).subtype Subtype.val_injective t).trans ht
  have hb := h.no_small_involutions (t : A) htA
  rw [hS, fixedCodim_zpowers_eq_displacement_rank] at hb
  rw [fixedCodim_zpowers_eq_displacement_rank] at hsmall
  exact (Nat.not_lt_of_ge hsmall) hb

omit [Finite A] in
/-- The pair bound applies to any two actual conjugates of the original actor. -/
theorem Input.conjugates_moved_finrank_le_three (h : Input ρ C) (hC3 : Nat.card C = 3)
    (a b : A)
    (hnc : ¬ ∀ c ∈ C.map (MulAut.conj a).toMonoidHom,
      ∀ d ∈ C.map (MulAut.conj b).toMonoidHom, Commute c d) :
    finrank (ZMod 2) ↥(displacementSpan ρ (C.map (MulAut.conj a).toMonoidHom) ⊤ ⊔
      displacementSpan ρ (C.map (MulAut.conj b).toMonoidHom) ⊤) ≤ 3 := by
  have hmap : (C.map (MulAut.conj (a⁻¹ * b)).toMonoidHom).map
      (MulAut.conj a).toMonoidHom = C.map (MulAut.conj b).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext c
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hnc' : ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj (a⁻¹ * b)).toMonoidHom,
      Commute c d := by
    intro hh
    apply hnc
    rintro _ ⟨c, hc, rfl⟩ d hd
    rw [← hmap] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    exact (hh c hc d' hd').map (MulAut.conj a).toMonoidHom
  have hb := h.pair_moved_finrank_le_three hC3 (a⁻¹ * b) hnc'
  let S := displacementSpan ρ C ⊤ ⊔
    displacementSpan ρ (C.map (MulAut.conj (a⁻¹ * b)).toMonoidHom) ⊤
  have hS : S.map (ρ a) =
      displacementSpan ρ (C.map (MulAut.conj a).toMonoidHom) ⊤ ⊔
        displacementSpan ρ (C.map (MulAut.conj b).toMonoidHom) ⊤ := by
    dsimp only [S]
    rw [Submodule.map_sup, ← displacementSpan_conjugate, map_top_action,
      ← displacementSpan_conjugate, map_top_action, hmap]
  rw [← hS, ← (Submodule.equivMapOfInjective (ρ a) (ρ.apply_bijective a).injective S).finrank_eq]
  exact hb

end Representation.RegularCyclicNormalClosure
