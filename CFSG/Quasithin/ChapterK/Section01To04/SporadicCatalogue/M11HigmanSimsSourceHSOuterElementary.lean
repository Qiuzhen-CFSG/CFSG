module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceHSOuterActors

/-!
# Elementary outer displacement on the original HS module

The marked source center vanishes in the faithful irreducible binary action.
Its resulting isomorphism with the literal HS carrier transports the certified
fixed-point-free five-element inverted by the elementary outer automorphism.
The commutator rank inequality forces displacement at least ten; the involution
upper bound gives equality. No degree-recognition or model-comparison input is
used. This discharges the involution field of `ElementaryOuterEstimates`.

Every elementary outer actor below rank five therefore has a strict ratio-two
gap. At rank five an actual five-element of the component in the centralizer
closure forces displacement at least eleven. The final source-actor application
retains the exact closure and reduces the elementary case to displacement ten
with no such five-element. Constructing the remaining rank-five obstruction and
the symmetric outer estimates is still required for `HigmanSimsOuterEstimates`.

Source: GM02 Proposition 5.1, HS paragraph, author preprint pp.16–17;
Aschbacher–Smith K.4, printed p.457/PDF p.468. The five-element argument replaces
the printed eleven-element inversion for the elementary outer involution only.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech
open HigmanSims
open Twenty
open Sporadic.LeechRelated.HS (Carrier)
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

omit [Finite G] in
private theorem five_displacement_le_twice {x t : G}
    (hx : orderOf x = 5) (hinv : t * x * t⁻¹ = x⁻¹) :
    fixedCodim ρ (zpowers x) ≤ 2 * fixedCodim ρ (zpowers t) := by
  have hz : zpowers (x ^ 2) = zpowers x := by
    apply le_antisymm
    · exact zpowers_le.mpr ((zpowers x).pow_mem (mem_zpowers x) 2)
    · apply zpowers_le.mpr
      rw [mem_zpowers_pow_iff, hx]
      decide
  have hb := fixedCodim_commutator_le_twice ρ t x
  rw [hinv, ← mul_inv_rev, ← pow_two, zpowers_inv, hz] at hb
  exact hb

/-- The elementary outer class moves at least ten dimensions on the original
source module, for every literal central-quotient marking. -/
theorem higmanSims_elementary_outer_involution_bound (h : HigmanSims.SourceHypotheses ρ)
    (hd : Module.finrank (ZMod 2) V = 20)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {t : G} (htE : IsElementaryOuter e t) : 10 ≤ fixedCodim ρ (zpowers t) := by
  let := h.quasisimple
  have hz := h.center_eq_bot_of_two_group
    (Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e)
  have hq : Function.Injective (QuotientGroup.mk' (center (generalizedFitting G))) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk', hz]
  let f : generalizedFitting G ≃* Carrier := MulEquiv.ofBijective
    (e.toMonoidHom.comp (QuotientGroup.mk' (center (generalizedFitting G))))
    ⟨e.injective.comp hq, e.surjective.comp (QuotientGroup.mk'_surjective _)⟩
  let σ := (ρ.comp (generalizedFitting G).subtype).comp f.symm.toMonoidHom
  have hf : Function.Injective σ :=
    (h.faithful.comp (generalizedFitting G).subtype_injective).comp f.symm.injective
  let r : MulAut Carrier := MulAut.centralQuotientAction e (MulAut.conjNormal t)
  have hr : IsConj
      (Sporadic.LeechRelated.HS.generated.normalizerMonoidHom
        Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.elementaryNormalizer) r := htE
  obtain ⟨x, hx, hi, hfree⟩ := HSOuterCalculations.elementary_inverts_free_five σ hf hd hr
  let y : generalizedFitting G := f.symm x
  have hxy : f y = x := f.apply_symm_apply x
  have hy : orderOf (y : G) = 5 := by
    exact (orderOf_injective (generalizedFitting G).subtype
      (generalizedFitting G).subtype_injective y).trans ((f.symm.orderOf_eq x).trans hx)
  have hyi : t * (y : G) * t⁻¹ = (y : G)⁻¹ := by
    have hact : f (MulAut.conjNormal t y) = r (f y) :=
      (MulAut.centralQuotientAction_apply e (MulAut.conjNormal t) y).symm
    have he : MulAut.conjNormal t y = y⁻¹ := by
      apply f.injective
      calc
        f (MulAut.conjNormal t y) = r (f y) := hact
        _ = r x := congrArg r hxy
        _ = x⁻¹ := hi
        _ = f (y⁻¹) := (congrArg Inv.inv hxy).symm.trans (f.map_inv y).symm
    exact congrArg Subtype.val he
  have hcodim : fixedCodim ρ (zpowers (y : G)) = 20 := by
    have he := fixedCodim_add_finrank σ (zpowers x)
    rw [hfree, finrank_bot, add_zero, hd] at he
    rw [fixedCodim_zpowers_eq_displacement_rank] at he ⊢
    exact he
  have hb := five_displacement_le_twice (ρ := ρ) hy hyi
  rw [hcodim] at hb
  omega

/-- The elementary outer involution has exactly ten-dimensional displacement. -/
theorem higmanSims_elementary_outer_involution_codim (h : HigmanSims.SourceHypotheses ρ)
    (hd : Module.finrank (ZMod 2) V = 20)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {t : G} (ht : t ^ 2 = 1) (htE : IsElementaryOuter e t) :
    fixedCodim ρ (zpowers t) = 10 := by
  have hb : 10 ≤ fixedCodim ρ (zpowers t) :=
    higmanSims_elementary_outer_involution_bound h hd e htE
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    have hz : fixedCodim ρ (zpowers (1 : G)) = 0 :=
      (fixedCodim_eq_zero_iff ρ _).mpr (by rw [zpowers_one_eq_bot, fixedSpace_bot])
    omega
  have hu := (involution_actor_rank_and_fixedCodim ρ t (orderOf_eq_prime ht ht1)).2.2.2
  rw [hd] at hu
  omega

omit [Finite G] in
private theorem codim_le_of_mem {A : Subgroup G} {t : G} (ht : t ∈ A) :
    fixedCodim ρ (zpowers t) ≤ fixedCodim ρ A := by
  have hm := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ht))
  have hA := fixedCodim_add_finrank ρ A
  have ht' := fixedCodim_add_finrank ρ (zpowers t)
  omega

/-- All elementary-outer actors below rank five have a strict ratio-two gap. -/
theorem higmanSims_elementary_outer_gap_of_rank_lt_five (h : HigmanSims.SourceHypotheses ρ)
    (hd : Module.finrank (ZMod 2) V = 20)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {A : Subgroup G} (hr : rank A < 5) {t : G} (htA : t ∈ A)
    (htE : IsElementaryOuter e t) : 2 * rank A < fixedCodim ρ A := by
  have hb := (higmanSims_elementary_outer_involution_bound h hd e htE).trans
    (codim_le_of_mem htA)
  omega

/-- The proved five-element bound transported to the actual source component. -/
theorem higmanSims_inner_order_five_bound (h : HigmanSims.SourceHypotheses ρ)
    (hd : Module.finrank (ZMod 2) V = 20) {x : G}
    (hxL : x ∈ generalizedFitting G) (hx : orderOf x = 5) :
    16 ≤ fixedCodim ρ (zpowers x) := by
  let := h.quasisimple
  obtain ⟨e⟩ := h.centralQuotient
  obtain ⟨f, σ, hf, _, hact⟩ := Inner.exists_marked_carrier_representation h
    (Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e)
  let y : generalizedFitting G := ⟨x, hxL⟩
  have hy : orderOf (f y) = 5 := (f.orderOf_eq y).trans
    ((orderOf_injective (generalizedFitting G).subtype
      (generalizedFitting G).subtype_injective y).symm.trans hx)
  have hb : 16 ≤ fixedCodim σ (zpowers (f y)) :=
    Inner.order_five_fixedCodim_ge_sixteen σ hf hd (f y) hy
  rw [fixedCodim_zpowers_eq_displacement_rank, hact y,
    ← fixedCodim_zpowers_eq_displacement_rank] at hb
  exact hb

/-- An actual component five-element in the literal centralizer closure
forces displacement at least eleven. The group-membership premise is explicit. -/
theorem higmanSims_elementary_outer_bound_of_closure_five
    (h : HigmanSims.SourceHypotheses ρ) (hd : Module.finrank (ZMod 2) V = 20)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {A : Subgroup G} {t : G} (htA : t ∈ A) (htE : IsElementaryOuter e t)
    {x : G} (hxC : x ∈ centralizerConjugateClosure A t)
    (hxL : x ∈ generalizedFitting G) (hx : orderOf x = 5) :
    11 ≤ fixedCodim ρ A := by
  have hb := higmanSims_inner_order_five_bound h hd hxL hx
  exact lt_fixedCodim_of_centralizerConjugateClosure_bound htA (zpowers_le.mpr hxC)
    (higmanSims_elementary_outer_involution_bound h hd e htE) (by omega)

/-- On an actual cubic source actor, the elementary outer branch is reduced
to rank five, displacement ten, and the absence of component five-elements in
its literal centralizer closure. The symmetric branch retains its actual marking. -/
theorem higmanSims_cubic_outer_cases (h : HigmanSims.SourceHypotheses ρ)
    (hd : Module.finrank (ZMod 2) V = 20)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    (rank A = 5 ∧ fixedCodim ρ A = 10 ∧
      ∃ t ∈ A, IsElementaryOuter e t ∧
        ∀ x ∈ centralizerConjugateClosure A t, x ∈ generalizedFitting G → orderOf x ≠ 5) ∨
      (∃ t ∈ A, t ^ 2 = 1 ∧ IsSymmetricOuter e t) := by
  let := hA.2
  have hnot := higmanSims_cubic_actor_not_le h hd hA hsmall
  obtain ⟨t, htA, htL⟩ := Set.not_subset.mp hnot
  have ht2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t htA
  rcases outer_involution_cases h e ht2 htL with htE | htS
  · have hb := (higmanSims_elementary_outer_involution_bound h hd e htE).trans
      (codim_le_of_mem htA)
    have hr := hA.rank_le_of_primeRank_le h.twoRank_le_five
    refine Or.inl ⟨by omega, by omega, t, htA, htE, ?_⟩
    intro x hxC hxL hx5
    have hc := higmanSims_elementary_outer_bound_of_closure_five h hd e htA htE hxC hxL hx5
    omega
  · exact Or.inr ⟨t, htA, ht2, htS⟩

end CFSG.Quasithin.ChapterK.SporadicCatalogue
