module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.QuotientActions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.Transport

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.EarlierFitting
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.KernelPlacement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.ParabolicPlacement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.NormalizerExclusion

/-!
# Covered residual placement and source actions

The literal earlier Fitting alternative 13.8.14 puts the two-perfect L₁*
inside K*F(H*). Noncontainment of L₁ in K forces F(H*) = X*, proving its
normality, cubic order and centralization of K*. The two marked T-invariant
lines in L₁/O₂(L₁) then place L₀ in K. Independently, the source normalizer
bound excludes L₀ as a centralizing direction: otherwise residual lifting
would put K in N_G(L₀) ≤ M.

The actual Sylow intersection and L₀* are marked at a concrete point or
line parabolic of SL₃(2), retaining its full embedded two-residual and its
surviving two-core. The natural covered action supplies the inverter in
T∩L and all three seed facts. Intrinsic commutator bounds preserve inversion
when the inverter is corrected by an element of O₂(L₀).

`source_placement` proves this conditional source branch from the actual
natural setup, 13.2.2(3),(9), the earlier Fitting alternative, relative
normality of K from 13.8.16(1), the source Sylow subgroup, and the given
K* ≃ SL₃(2). It assumes no residual placement or product equivalence.
The S₃ centralizer, full product and tensor exclusion belong to the consumer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
covered paragraph of 13.8.21(1), printed p.957, with Notation 13.2.1.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G]

/-- After component centralization is proved, the actual residual definitions supply the remaining normality inputs. -/
theorem plus_star_normal (H K L T V₁ : Subgroup G)
    (hgen : H = K ⊔ (one L T V₁ ⊔ T)) (hKH : K ≤ H)
    (hLH : one L T V₁ ≤ H) (hTH : T ≤ H)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hcentral : Source.starImage H K ≤
      centralizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H))) :
    (Source.starImage H (plus L T V₁)).Normal :=
  star_normal_of_source_generators H K (one L T V₁) T (plus L T V₁)
    hgen hKH hLH hTH hcentral (one_normalizes_plus L T V₁)
    (T_normalizes_plus L T V₁ hTL hTV)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The factorization in 13.2.2(3) gives the actual set product in H*,
as well as the join equality used by subgroup APIs. -/
theorem one_star_factorization (H L T V₁ : Subgroup G)
    (hDH : one L T V₁ ≤ H) (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hn : (Source.starImage H (plus L T V₁)).Normal) :
    Source.starImage H (one L T V₁) =
      Source.starImage H (plus L T V₁) ⊔ Source.starImage H (zero L) ∧
    (Source.starImage H (one L T V₁) : Set (Source.Hstar H)) =
      (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)) *
      (Source.starImage H (zero L) : Set (Source.Hstar H)) := by
  have he : Source.starImage H (one L T V₁) =
      Source.starImage H (plus L T V₁) ⊔ Source.starImage H (zero L) := by
    rw [hfactor, star_sup H _ _ ((plus_le_one L T V₁ hTV).trans hDH)
      ((LocalAction.zero_le_one_of_factorization L T V₁ hfactor).trans hDH)]
  refine ⟨he, ?_⟩
  rw [he]
  exact coe_mul_of_right_le_normalizer_left _ _ le_normalizer_of_normal

/-- Covered residual placement from the literal earlier source inputs.
13.2.2(3), 13.8.14 and 13.8.16(1) remain explicit, alongside the marked
natural action, the source Sylow subgroup, and the actual K* model.
All placement, centralization, normality, cubic order, parabolic marking,
inverter and seed conclusions are derived. -/
theorem source_placement (H K L T V V₁ V₃ M : Subgroup G)
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (one L T V₁ ⊔ T))
    (hnot : ¬ one L T V₁ ≤ K)
    (hKM : ¬ K ≤ M) (hNM : normalizer (zero L : Set G) ≤ M)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (hfit : fittingPreimageResidual H = ⊥ ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        fittingPreimageResidual H = one L T V₁) ∨
      fittingPreimageResidual H = plus L T V₁) :
    zero L ≤ K ∧
    (¬ K ≤ normalizer (zero L : Set G)) ∧
    (¬ Source.starImage H K ≤ centralizer (Source.starImage H (zero L) : Set (Source.Hstar H))) ∧
    Source.starImage H K ≤ centralizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)) ∧
    (Source.starImage H (plus L T V₁)).Normal ∧
    Nat.card (Source.starImage H (plus L T V₁)) = 3 ∧
    (Source.starImage H (one L T V₁) : Set (Source.Hstar H)) =
      (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)) *
      (Source.starImage H (zero L) : Set (Source.Hstar H)) ∧
    Nonempty (ParabolicPlacement H K L T eK) ∧
    (plus L T V₁ ≤ normalizer (V₃ : Set G) ∧
      V₃ ≤ ⁅plus L T V₁, V₃⁆ ⊔ V₁ ∧ ⁅zero L, V₃⁆ ≤ V₁) ∧
    ∃ t : (T ⊓ L : Subgroup G), ∃ htH : t.val ∈ H,
      (∀ x : plus L T V₁ ⧸ pCore 2 (plus L T V₁), coreAction (plus L T V₁)
        ⟨t.val, T_normalizes_plus L T V₁ d.normalizes_L d.line_stable t.property.1⟩ x = x⁻¹) ∧
      coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 ∧
      (∀ x ∈ Source.starImage H (plus L T V₁),
        QuotientGroup.mk' (pCore 2 H) ⟨t.val, htH⟩ * x *
          (QuotientGroup.mk' (pCore 2 H) ⟨t.val, htH⟩)⁻¹ = x⁻¹) := by
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hDH : one L T V₁ ≤ H := by rw [hgen]; exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  have hXH := (plus_le_one L T V₁ d.line_stable).trans hDH
  have hfit' := fitting_alternative_image H L T V₁
    (covered_fitting_alternative H L T V₁ d.cover hfit)
  obtain ⟨_, hn, hc, hDX, hcentral⟩ :=
    component_centralization H K L T V V₁ V₃ d hfactor hgen hnot eK hfit'
  have hz := zero_le_component H K L T V V₁ V₃ d hfactor hKH hDH hTH eK hc hDX hcentral
  have hpar := exists_zero_parabolic H K L T V V₁ V₃ d hKH hTH hz S hS eK
  have he := (one_star_factorization H L T V₁ hDH d.line_stable hfactor hn).2
  have hexclude := zero_not_star_centralizing H K L T V₁ M hKH hDH d.normalizes_L
    hfactor S hS hKM hNM
  obtain ⟨t, ht, ht₀⟩ := d.exists_plus_inverter hfactor
  refine ⟨hz, (fun hn => hKM (hn.trans hNM)), hexclude, hcentral, hn, hc, he, hpar,
    d.seed_facts hfactor, t, hTH t.property.1, ht, ht₀, ?_⟩
  exact normal_star_inversion H _ hXH hn
    ⟨t.val, T_normalizes_plus L T V₁ d.normalizes_L d.line_stable t.property.1⟩
    (hTH t.property.1) ht

/-- Every element of the placed L₀ acts trivially on X/O₂(X). In particular
this applies to corrections from O₂(L₀), even when their star images survive. -/
theorem zero_adjustment_action (H K L T V₁ : Subgroup G)
    (hKH : K ≤ H) (hDH : one L T V₁ ≤ H)
    (hTV : T ≤ normalizer (V₁ : Set G)) (hzero : zero L ≤ K)
    (hn : (Source.starImage H (plus L T V₁)).Normal)
    (hcentral : Source.starImage H K ≤
      centralizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)))
    (c : normalizer (plus L T V₁ : Set G)) (hc : c.val ∈ zero L) :
    coreAction (plus L T V₁) c = 1 := by
  apply coreAction_eq_one_of_star_centralizes H _ ((plus_le_one L T V₁ hTV).trans hDH)
    hn c (hKH (hzero hc))
  exact hcentral ⟨⟨c.val, hKH (hzero hc)⟩, hzero hc, rfl⟩

/-- The actual local commutators lie in O₂(X), so no ambient-core quotient
is used to erase the surviving two-core of L₀*. -/
theorem zero_adjustment_commutator (H K L T V₁ : Subgroup G)
    (hKH : K ≤ H) (hDH : one L T V₁ ≤ H)
    (hTV : T ≤ normalizer (V₁ : Set G)) (hzero : zero L ≤ K)
    (hn : (Source.starImage H (plus L T V₁)).Normal)
    (hcentral : Source.starImage H K ≤
      centralizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)))
    (c : normalizer (plus L T V₁ : Set G)) (hc : c.val ∈ zero L)
    (x : plus L T V₁) :
    (plus L T V₁).normalizerMonoidHom c x * x⁻¹ ∈ pCore 2 (plus L T V₁) :=
  (coreAction_eq_one_iff _ c).mp
    (zero_adjustment_action H K L T V₁ hKH hDH hTV hzero hn hcentral c hc) x

/-- Multiplying the source inverter by a normalizing element of O₂(L₀)
preserves inversion through the original intrinsic quotient action. -/
theorem zero_core_inversion_preserved (H K L T V₁ : Subgroup G)
    (hKH : K ≤ H) (hDH : one L T V₁ ≤ H)
    (hTV : T ≤ normalizer (V₁ : Set G)) (hzero : zero L ≤ K)
    (hn : (Source.starImage H (plus L T V₁)).Normal)
    (hcentral : Source.starImage H K ≤
      centralizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)))
    (t c : normalizer (plus L T V₁ : Set G)) (hc : c.val ∈ (zero L).pCoreIn 2)
    (ht : ∀ q : plus L T V₁ ⧸ pCore 2 (plus L T V₁), coreAction (plus L T V₁) t q = q⁻¹) :
    ∀ q : plus L T V₁ ⧸ pCore 2 (plus L T V₁), coreAction (plus L T V₁) (t * c) q = q⁻¹ := by
  intro q
  rw [map_mul, zero_adjustment_action H K L T V₁ hKH hDH hTV hzero hn hcentral c
    (pCoreIn_le 2 (zero L) hc), mul_one]
  exact ht q

omit [Finite G] in
/-- The actual correction subgroup normalizes X by relative normality in L₁. -/
theorem zero_core_normalizes_plus (L T V₁ : Subgroup G)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    (zero L).pCoreIn 2 ≤ normalizer (plus L T V₁ : Set G) :=
  (pCoreIn_le 2 (zero L)).trans
    ((LocalAction.zero_le_one_of_factorization L T V₁ hfactor).trans (one_normalizes_plus L T V₁))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
