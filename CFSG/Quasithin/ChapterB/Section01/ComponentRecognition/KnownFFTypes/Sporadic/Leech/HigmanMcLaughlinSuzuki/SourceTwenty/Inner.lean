module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Inner degree-twenty Higman--Sims displacement: order-five reduction

An involution inverting an element x of order five has displacement at least
half that of x: the commutator with x is x⁻², which generates the same cyclic
subgroup. The two checked HS involution classes then give displacement at
least eight, and exactly ten for the product class when its inverted five-element
acts without fixed points. Thus an actor moving at most eight dimensions is
2A-pure. If a rank-four actor's centralizer closure contains a five-element,
the common-fixed-space argument excludes displacement eight.

The source transport removes a two-group center and constructs a marked HS
representation on the same vector space, retaining its pointwise action
equation. Both elementary rank and fixed codimension are transported through
this actual isomorphism. The final theorem applies the resulting estimates
to `Twenty.inner_gap_of_estimates`.

The cover-center bound, universal order-five restrictions, and the concrete
centralizer-closure construction remain explicit inputs. This module does
not yet assert the unconditional source estimates. The centralizer input
uses the actual nonsplit core/S₅ extension, with no A₅ complement assumption.

Source: Guralnick--Malle, *Classification of 2F-modules, I*, Proposition 5.1,
HS paragraph, preprint pp.16--17; Aschbacher--Smith K.4, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace Twenty.Inner
universe u v
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem five_displacement_le_twice {D : Type*} [Group D]
    (σ : Representation (ZMod 2) D V) {x t : D}
    (hx : orderOf x = 5) (hinv : t * x * t⁻¹ = x⁻¹) :
    fixedCodim σ (zpowers x) ≤ 2 * fixedCodim σ (zpowers t) := by
  have hz : zpowers (x ^ 2) = zpowers x := by
    apply le_antisymm
    · exact zpowers_le.mpr ((zpowers x).pow_mem (mem_zpowers x) 2)
    · apply zpowers_le.mpr
      rw [mem_zpowers_pow_iff, hx]
      decide
  have hb := fixedCodim_commutator_le_twice σ t x
  rw [hinv, ← mul_inv_rev, ← pow_two, zpowers_inv, hz] at hb
  exact hb

private theorem codim_of_isConj {D : Type*} [Group D]
    (σ : Representation (ZMod 2) D V) {a b : D} (hab : IsConj a b) :
    fixedCodim σ (zpowers b) = fixedCodim σ (zpowers a) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  rw [← hg]
  exact fixedCodim_zpowers_conj σ a g

private theorem codim_le_of_mem {D : Type*} [Group D]
    (σ : Representation (ZMod 2) D V) {A : Subgroup D} {t : D} (ht : t ∈ A) :
    fixedCodim σ (zpowers t) ≤ fixedCodim σ A := by
  have hm := Submodule.finrank_mono (fixedSpace_antitone σ (zpowers_le.mpr ht))
  have hA := fixedCodim_add_finrank σ A
  have ht' := fixedCodim_add_finrank σ (zpowers t)
  omega

/-- Inverting a five-element that moves at least sixteen dimensions gives
GM's lower bound for the central involution class. -/
theorem core_involution_bound (σ : Representation (ZMod 2) HS V)
    (hfive : FiveRestrictions σ) {t : HS} (ht : IsConj coreInvolution t) :
    8 ≤ fixedCodim σ (zpowers t) := by
  obtain ⟨x, hx, hi⟩ := hfive.core_inverts
  have h1 := five_displacement_le_twice σ hx hi
  have h2 := hfive.order_five x hx
  rw [codim_of_isConj σ ht]
  omega

/-- The product class has displacement exactly ten on a degree-twenty module.
The upper bound is the square-zero displacement inequality in characteristic two. -/
theorem product_involution_codim (σ : Representation (ZMod 2) HS V)
    (hd : Module.finrank (ZMod 2) V = 20) (hfive : FiveRestrictions σ)
    {t : HS} (ht : IsConj productInvolution t) (ht2 : orderOf t = 2) :
    fixedCodim σ (zpowers t) = 10 := by
  obtain ⟨x, hx, hi, hf⟩ := hfive.product_inverts_free
  have h1 := five_displacement_le_twice σ hx hi
  have h2 := fixedCodim_add_finrank σ (zpowers x)
  rw [hf, finrank_bot, add_zero, hd] at h2
  let : Finite HS := _root_.Sporadic.LeechRelated.HS.carrierFinite
  have h3 := (involution_actor_rank_and_fixedCodim σ t ht2).2.2.2
  rw [hd] at h3
  rw [h2, ← codim_of_isConj σ ht] at h1
  omega

/-- The checked two-class coverage makes the lower bound exhaustive. -/
theorem involution_bound (σ : Representation (ZMod 2) HS V)
    (hd : Module.finrank (ZMod 2) V = 20) (hfive : FiveRestrictions σ)
    {t : HS} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    8 ≤ fixedCodim σ (zpowers t) := by
  have ho : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  rcases Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.involution_classes t ho with hc | hp
  · exact core_involution_bound σ hfive hc
  · rw [product_involution_codim σ hd hfive hp ho]
    decide

/-- An elementary actor of displacement at most eight must be 2A-pure.
This is the precise class-exclusion step before using the centralizer. -/
theorem core_pure_of_codim_le_eight (σ : Representation (ZMod 2) HS V)
    (hd : Module.finrank (ZMod 2) V = 20) (hfive : FiveRestrictions σ)
    {A : Subgroup HS} (hA : IsElementaryTwo A) (hcodim : fixedCodim σ A ≤ 8)
    {t : HS} (ht : t ∈ A) (ht1 : t ≠ 1) : IsConj coreInvolution t := by
  let := hA.2
  have ho : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht) ht1
  rcases Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.involution_classes t ho with hc | hp
  · exact hc
  · have htD := product_involution_codim σ hd hfive hp ho
    have hm := codim_le_of_mem σ ht
    omega

/-- An actual five-element in the centralizer closure excludes equality eight.
No splitting of the centralizer extension is used. -/
theorem rank_four_bound (σ : Representation (ZMod 2) HS V)
    (hd : Module.finrank (ZMod 2) V = 20) (hfive : FiveRestrictions σ)
    (hclosure : CoreClosureFive) {A : Subgroup HS}
    (hA : IsElementaryTwo A) (hr : rank A = 4) : 9 ≤ fixedCodim σ A := by
  by_contra! hn
  have hcodim : fixedCodim σ A ≤ 8 := by omega
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hc := core_pure_of_codim_le_eight σ hd hfive hA hcodim ht ht1
  obtain ⟨x, hx, hx5⟩ := hclosure A hA hr t ht hc
  let := hA.2
  have ht2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht
  have hb := lt_fixedCodim_of_centralizerConjugateClosure_bound
    (ρ := σ) (K := zpowers x) (d := 8) ht (zpowers_le.mpr hx)
    (involution_bound σ hd hfive ht1 ht2) (by have := hfive.order_five x hx5; omega)
  omega

variable {G : Type u} [Group G] [Finite G]
  {ρ : Representation (ZMod 2) G V}

/-- Removing the two-group center retains the actual group marking and the
pointwise action equation, in addition to faithfulness and irreducibility. -/
theorem exists_marked_carrier_representation (h : SourceHypotheses ρ)
    (hcenter : IsPGroup 2 (center (generalizedFitting G))) :
    ∃ (f : generalizedFitting G ≃* HS) (σ : Representation (ZMod 2) HS V),
      Function.Injective σ ∧ σ.IsIrreducible ∧
      ∀ g : generalizedFitting G, σ (f g) = ρ (g : G) := by
  obtain ⟨e⟩ := h.centralQuotient
  let q : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃*
      generalizedFitting G :=
    (QuotientGroup.quotientMulEquivOfEq (h.center_eq_bot_of_two_group hcenter)).trans
      QuotientGroup.quotientBot
  let f := q.symm.trans e
  let τ := ρ.comp (generalizedFitting G).subtype
  let σ := τ.comp f.symm.toMonoidHom
  refine ⟨f, σ, (h.faithful.comp (generalizedFitting G).subtype_injective).comp
    f.symm.injective, ?_, ?_⟩
  · exact (Representation.irreducible_comp_surjective_iff
      f.symm.toMonoidHom f.symm.surjective τ).mpr h.irreducible
  · intro g
    change ρ ((f.symm (f g) : generalizedFitting G) : G) = ρ (g : G)
    rw [f.symm_apply_apply]

/-- Assemble both inner estimates on the original representation. The source
cover-center bound, universal cyclic restrictions, and actual centralizer
closure construction remain explicit undischarged inputs. -/
theorem estimates_of_inputs (h : SourceHypotheses ρ)
    (hd : Module.finrank (ZMod 2) V = 20)
    (hcenter : IsPGroup 2 (center (generalizedFitting G)))
    (hfive : ∀ σ : Representation (ZMod 2) HS V,
      Function.Injective σ → σ.IsIrreducible →
      Module.finrank (ZMod 2) V = 20 → FiveRestrictions σ)
    (hclosure : CoreClosureFive) : InnerEstimates ρ := by
  obtain ⟨f, σ, hf, hi, hact⟩ := exists_marked_carrier_representation h hcenter
  have hF := hfive σ hf hi hd
  constructor
  · intro t htL ht1 ht2
    let s : generalizedFitting G := ⟨t, htL⟩
    have hs1 : f s ≠ 1 := by
      intro he
      have he' : s = 1 := f.injective (he.trans (map_one f).symm)
      exact ht1 (congrArg Subtype.val he')
    have hs2 : (f s) ^ 2 = 1 := by
      rw [← map_pow]
      have he : s ^ 2 = 1 := Subtype.ext ht2
      rw [he, map_one]
    have hb := involution_bound σ hd hF hs1 hs2
    rw [fixedCodim_zpowers_eq_displacement_rank, hact s,
      ← fixedCodim_zpowers_eq_displacement_rank] at hb
    exact hb
  · intro A hA hAL hr
    let B := A.subgroupOf (generalizedFitting G)
    let D := B.map f.toMonoidHom
    have hrD : rank D = 4 := by
      rw [rank_map_injective f.toMonoidHom f.injective,
        ← rank_map_injective (generalizedFitting G).subtype
          (generalizedFitting G).subtype_injective B]
      simpa only [B, map_subgroupOf_eq_of_le hAL] using hr
    let := hA.2
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAL
    have hD : IsElementaryTwo D := by
      refine ⟨?_, IsElementaryAbelian.map f.toMonoidHom⟩
      intro he
      rw [he, Representation.BinaryOffender.rank_bot] at hrD
      omega
    have hb := rank_four_bound σ hd hF hclosure hD hrD
    have he := fixedCodim_map_equivariant
      (ρ.comp (generalizedFitting G).subtype) σ f.toMonoidHom
      (LinearEquiv.refl (ZMod 2) V)
      (fun g v => (congrArg (fun a : Module.End (ZMod 2) V => a v) (hact g)).symm) B
    have he' : fixedCodim (ρ.comp (generalizedFitting G).subtype) B =
        fixedCodim ρ A := by
      unfold fixedCodim
      change Module.finrank (ZMod 2)
        (V ⧸ fixedSpace (ρ.comp (generalizedFitting G).subtype)
          (A.subgroupOf (generalizedFitting G))) = _
      rw [fixedSpace_comp_map, Subgroup.map_subgroupOf_eq_of_le hAL]
    rw [← he, he'] at hb
    exact hb

/-- Application to the specified strict inner gap consumer. This theorem
retains all three remaining source inputs, so is not an unconditional HS bound. -/
theorem gap_of_inputs (h : SourceHypotheses ρ)
    (hd : Module.finrank (ZMod 2) V = 20)
    (hcenter : IsPGroup 2 (center (generalizedFitting G)))
    (hfive : ∀ σ : Representation (ZMod 2) HS V,
      Function.Injective σ → σ.IsIrreducible →
      Module.finrank (ZMod 2) V = 20 → FiveRestrictions σ)
    (hclosure : CoreClosureFive)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ generalizedFitting G) :
    2 * rank A < fixedCodim ρ A :=
  inner_gap_of_estimates h (estimates_of_inputs h hd hcenter hfive hclosure) hA hAL

end Twenty.Inner
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
