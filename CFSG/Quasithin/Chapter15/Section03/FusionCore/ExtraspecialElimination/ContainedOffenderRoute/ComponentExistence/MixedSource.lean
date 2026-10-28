module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.Preparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.Mixed
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.GroupCore

/-!
# The full mixed source alternative yields a contradiction

For B.5.6(4), the quotient by the displayed product is cyclic. Generation
by binary best offenders forces its generator to have square one, and the
outer action on the cyclic three-factor makes that generator nontrivial.
Thus the product has index two. Transport of the same outer action to C₃
proves inversion of its marked generator. These are the precise inputs
consumed by the mixed-case core calculation.

Consequently the literal OuterSixThreeCase on the selected star action is
impossible for PlacedInput. Both allowed dimensions of the A₆ moved space
are covered; no endpoint equality or solvability of M ∩ H is required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(4),
printed p.105, and proof of 15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
open ComponentReduction
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

private theorem cubic_auto_inverts (α : MulAut (Multiplicative (ZMod 3)))
    (hne : α ≠ MulEquiv.refl _) :
    α (Multiplicative.ofAdd 1) = (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ := by
  have he : ∀ f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3),
      f 1 = 1 → (∀ x y, f (x * y) = f x * f y) → Function.Injective f →
      (∃ x, f x ≠ x) → f (Multiplicative.ofAdd 1) = (Multiplicative.ofAdd 1)⁻¹ := by
    decide +kernel
  apply he α (map_one α) (map_mul α) α.injective
  by_contra! hh
  exact hne (MulEquiv.ext hh)

private theorem outer_cubic_inverts {D : Type*} [Group D]
    (C : Subgroup D) (e : C ≃* Multiplicative (ZMod 3)) (t : D)
    (h : InducesOuter C t) :
    t * (e.symm (Multiplicative.ofAdd 1) : D) * t⁻¹ =
      (e.symm (Multiplicative.ofAdd 1) : D)⁻¹ := by
  obtain ⟨α, ha, hn⟩ := h
  let β := e.symm.trans (α.trans e)
  have hb : β ≠ MulEquiv.refl _ := by
    intro he
    have heα : α = MulEquiv.refl _ := by
      apply MulEquiv.ext
      intro c
      apply e.injective
      have hh := congrArg (fun f : MulAut (Multiplicative (ZMod 3)) => f (e c)) he
      simpa only [β, MulEquiv.trans_apply, e.symm_apply_apply, MulEquiv.refl_apply] using hh
    apply hn
    exact ⟨1, by rw [map_one]; exact heα.symm⟩
  have hi := cubic_auto_inverts β hb
  have hai : α (e.symm (Multiplicative.ofAdd 1)) =
      (e.symm (Multiplicative.ofAdd 1))⁻¹ := by
    apply e.injective
    simpa only [β, MulEquiv.trans_apply, map_inv, e.apply_symm_apply] using hi
  rw [← ha]
  exact congrArg Subtype.val hai

universe u v
variable {D : Type u} [Group D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- Derive the index-two presentation and marked inversion from the full
source alternative and generation by best offenders. -/
theorem outerSixThree_presentation (c : OuterSixThreeCase ρ)
    (hg : offenderSubgroup ρ = ⊤) :
    ∃ (K : Subgroup D) (e : K ≃* alternatingGroup (Fin 6) × Multiplicative (ZMod 3))
      (t : D), K.index = 2 ∧
      t * (e.symm (1, Multiplicative.ofAdd 1) : K) * t⁻¹ =
        ((e.symm (1, Multiplicative.ofAdd 1) : K) : D)⁻¹ := by
  let K := c.first ⊔ c.second
  let e : K ≃* alternatingGroup (Fin 6) × Multiplicative (ZMod 3) :=
    c.product.symm.trans (c.firstEquiv.prodCongr c.secondEquiv)
  let := c.product_normal
  let := c.quotient_isCyclic
  let := IsCyclic.commGroup (α := D ⧸ K)
  let q := QuotientGroup.mk' K
  have hgen : zpowers (q c.element) = ⊤ := by
    have h := congrArg (Subgroup.map q) c.generates
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      MonoidHom.map_zpowers, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    exact h
  have hpow : q c.element ^ 2 = 1 := by
    let f : D →* (D ⧸ K) := (powMonoidHom 2).comp q
    have hle : offenderSubgroup ρ ≤ f.ker := by
      apply iSup_le
      intro A
      apply iSup_le
      rintro ⟨hA, _⟩ a ha
      let : IsElementaryAbelian 2 A := hA.1.2
      change q a ^ 2 = 1
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian a ha, map_one]
    rw [hg] at hle
    exact hle (mem_top _)
  have hinv := outer_cubic_inverts c.second c.secondEquiv c.element c.secondOuter
  have hmarked : ((e.symm (1, Multiplicative.ofAdd 1) : K) : D) =
      (c.secondEquiv.symm (Multiplicative.ofAdd 1) : D) := by
    change (c.product (c.firstEquiv.symm 1, c.secondEquiv.symm _) : D) = _
    rw [map_one, c.product_apply, Subgroup.coe_one, one_mul]
  have hnontrivial : q c.element ≠ 1 := by
    intro hh
    have ht : c.element ∈ K := (QuotientGroup.eq_one_iff _).mp hh
    obtain ⟨⟨a, b⟩, hab⟩ := c.product.surjective ⟨c.element, ht⟩
    have hcomm (s : c.second) : c.element * (s : D) = (s : D) * c.element := by
      have hbs : b * s = s * b := c.secondEquiv.injective (by simp only [map_mul, mul_comm])
      have heq : (a, b) * (1, s) = (1, s) * (a, b) := by
        ext <;> simp only [Prod.mk_mul_mk, mul_one, one_mul, hbs]
      have h := congrArg (fun p => (c.product p : D)) heq
      simpa only [map_mul, coe_mul, hab, c.product_apply, coe_one, one_mul] using h
    have hh' := hcomm (c.secondEquiv.symm (Multiplicative.ofAdd 1))
    rw [hh', mul_inv_cancel_right] at hinv
    have hci : c.secondEquiv.symm (Multiplicative.ofAdd 1) =
        (c.secondEquiv.symm (Multiplicative.ofAdd 1))⁻¹ := Subtype.ext hinv
    have heq := congrArg c.secondEquiv hci
    simp only [map_inv, c.secondEquiv.apply_symm_apply] at heq
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 3)) ≠
      (Multiplicative.ofAdd (1 : ZMod 3))⁻¹) heq
  refine ⟨K, e, c.element, ?_, ?_⟩
  · rw [index_eq_card, ← orderOf_eq_card_of_zpowers_eq_top hgen]
    exact orderOf_eq_prime hpow hnontrivial
  · simpa only [hmarked] using hinv

variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y W Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y W Y0 T ZS Z E)

/-- Eliminate the complete B.5.6(4) record on the actual selected star action. -/
theorem not_outerSixThreeCase (c : OuterSixThreeCase (starAction d)) : False := by
  obtain ⟨K, e, t, hi, ht⟩ := outerSixThree_presentation (starAction d) c
    (starHypothesis d).generated
  exact not_a6_cyclic_three_extension d K hi e t ht

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
