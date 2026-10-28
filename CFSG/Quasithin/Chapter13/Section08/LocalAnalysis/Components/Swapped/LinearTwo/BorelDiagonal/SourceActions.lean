module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceActions.MarkedImages
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceActions.TorusActions

/-!
# Source marked torus actions in the moving PSL₂ orbit

For the marked product coordinates constructed by ProductCoordinates, the
index-two component normalizer makes the moving element exchange both
binary Borel axes. Every element of T preserves both or exchanges both.
These statements descend to the literal SourceTorus.normalizerAction.

The images of L₀ = zero L and L₁,+ = plus L T V₁ are formed using the
actual toCommonTori map. Its restricted kernels are the intrinsic two-cores,
so the cubic quotient orders give cubic image orders. Normalization gives
invariance under the moving element. Membership in L gives pointwise
fixation of L₀'s image; the supplied local inverter gives pointwise inversion
of L₁,+'s image. The embedded two-residual still surjects equivariantly, so
the actual [B,s] prime restriction transports to the torus displacement.

This is conditional source transport for Aschbacher–Smith, proof of
13.8.16(1), printed p.952/PDF p.969; markings are Notation 13.2.1, p.877.
The earlier marked containments, quotient orders and inverter remain local
inputs. Final n = 2, L₁ = O²(B₀), and full projected images are the parent's
assembly, rather than conclusions of this transport leaf.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
variable (H K₀ : Subgroup G) (hK : K₀ ≤ H)
  (e : Source.starImage H K₀ ≃* Q × Q)
  (S : Sylow 2 (Source.starImage H K₀))
variable {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
local notation "B₀" => SourceTorus.chosenLift H K₀ hK S
local notation "f" => SourceTorus.toCommonTori H K₀ hK e S hn hmodel
local notation "C" => CommonTorus H K₀ e S

/-- The actual torus image of L₀ from Notation 13.2.1. -/
noncomputable def D₀ (L : Subgroup G) : Subgroup (C × C) := Markings.image B₀ (zero L) f

/-- The actual torus image of L₁,+ from Notation 13.2.1. -/
noncomputable def Dplus (L T V₁ : Subgroup G) : Subgroup (C × C) :=
  Markings.image B₀ (plus L T V₁) f

/-- The kernel calculation applies to each of the literal marked groups. -/
theorem marked_kernel (X : Subgroup G) (hXB : X ≤ B₀) :
    ((f).comp (inclusion hXB)).ker = pCore 2 X := by
  apply Markings.restriction_ker B₀ X hXB f
  · rw [SourceTorus.toCommonTori_ker]
    exact pCore_isPGroup
  · exact commonTori_odd H K₀ e S hn hmodel

/-- The actual quotient identification, retaining each representative's image. -/
noncomputable def markedQuotientEquiv (X : Subgroup G) (hXB : X ≤ B₀) :
    (X ⧸ pCore 2 X) ≃* Markings.image B₀ X f :=
  Markings.quotientEquiv B₀ X hXB f
    (by rw [SourceTorus.toCommonTori_ker]; exact pCore_isPGroup)
    (commonTori_odd H K₀ e S hn hmodel)

theorem markedQuotientEquiv_mk (X : Subgroup G) (hXB : X ≤ B₀) (x : X) :
    (markedQuotientEquiv H K₀ hK e S hn hmodel X hXB (QuotientGroup.mk' _ x) : C × C) =
      f (inclusion hXB x) := rfl

/-- Source markings give cubic invariant images with their distinct pointwise actions.
Containment, T-normalization, cubic quotient orders and the source inverter
are the precise earlier local inputs; no product action identity is assumed. -/
theorem marked_actions (L T V₁ : Subgroup G)
    (hLB : one L T V₁ ≤ B₀)
    (hzero : zero L ≤ one L T V₁) (hplus : plus L T V₁ ≤ one L T V₁)
    (hTB : T ≤ normalizer (B₀ : Set G))
    (hTzero : T ≤ normalizer (zero L : Set G))
    (hTplus : T ≤ normalizer (plus L T V₁ : Set G))
    (hc₀ : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hcplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    {t s : G} (ht : t ∈ T) (hs : s ∈ T ⊓ L)
    (hinv : ∀ u : plus L T V₁ ⧸ pCore 2 (plus L T V₁),
      coreAction (plus L T V₁) ⟨s, hTplus hs.1⟩ u = u⁻¹) :
    let τ := SourceTorus.normalizerAction H K₀ hK e S hn hmodel ⟨t, hTB ht⟩
    let α := SourceTorus.normalizerAction H K₀ hK e S hn hmodel ⟨s, hTB hs.1⟩
    Nat.card (D₀ H K₀ hK e S hn hmodel L) = 3 ∧
    Nat.card (Dplus H K₀ hK e S hn hmodel L T V₁) = 3 ∧
    (D₀ H K₀ hK e S hn hmodel L).map τ.toMonoidHom = D₀ H K₀ hK e S hn hmodel L ∧
    (Dplus H K₀ hK e S hn hmodel L T V₁).map τ.toMonoidHom =
      Dplus H K₀ hK e S hn hmodel L T V₁ ∧
    (∀ z ∈ D₀ H K₀ hK e S hn hmodel L, α z = z) ∧
    (∀ z ∈ Dplus H K₀ hK e S hn hmodel L T V₁, α z = z⁻¹) := by
  have hk : IsPGroup 2 (f).ker := by rw [SourceTorus.toCommonTori_ker]; exact pCore_isPGroup
  have ho := commonTori_odd H K₀ e S hn hmodel
  have heq (g : normalizer (B₀ : Set G)) (b : B₀) :
      SourceTorus.normalizerAction H K₀ hK e S hn hmodel g (f b) =
        f ((B₀).normalizerMonoidHom g b) :=
    SourceTorus.normalizerAction_toCommonTori H K₀ hK e S hn hmodel g b
  refine ⟨(Markings.image_card B₀ (zero L) (hzero.trans hLB) f hk ho).trans hc₀,
    (Markings.image_card B₀ (plus L T V₁) (hplus.trans hLB) f hk ho).trans hcplus,
    Markings.image_invariant B₀ (zero L) f ⟨t, hTB ht⟩ (hTzero ht) _ (heq _),
    Markings.image_invariant B₀ (plus L T V₁) f ⟨t, hTB ht⟩ (hTplus ht) _ (heq _),
    ?_, ?_⟩
  · exact Markings.image_fixed B₀ (zero L) (hzero.trans hLB) f hk ho
      ⟨s, hTB hs.1⟩ (hTzero hs.1) _ (heq _)
      (L_centralizes_zero_quotient L ⟨s, hs.2⟩)
  · exact Markings.image_inverted B₀ (plus L T V₁) (hplus.trans hLB) f hk ho
      ⟨s, hTB hs.1⟩ (hTplus hs.1) _ (heq _) hinv

omit [Finite Q] in
/-- Normalized marked subgroups have invariant full binary images as well.
This retains their two-cores for the later ProjectedImages application. -/
theorem binary_image_invariant (X : Subgroup G) {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G))
    (hgB : g ∈ normalizer (B₀ : Set G)) (hgX : g ∈ normalizer (X : Set G)) :
    ((X.subgroupOf B₀).map (SourceTorus.toBinary H K₀ hK e S)).map
      (binaryAction H K₀ hK e S hgH hgK hgB).toMonoidHom =
        (X.subgroupOf B₀).map (SourceTorus.toBinary H K₀ hK e S) :=
  Markings.image_invariant B₀ X (SourceTorus.toBinary H K₀ hK e S)
    ⟨g, hgB⟩ hgX _ (binaryAction_toBinary H K₀ hK e S hgH hgK hgB)

/-- B is the embedded two-residual O²(B₀). -/
abbrev residualBorel : Subgroup G := (pResidual 2 B₀).map (B₀).subtype

/-- Restrict the existing torus map to the actual embedded two-residual. -/
noncomputable def residualMap : residualBorel H K₀ hK S →* C × C :=
  (f).comp (inclusion (map_subtype_le (pResidual 2 B₀)))

theorem residualMap_surjective : Function.Surjective (residualMap H K₀ hK e S hn hmodel) :=
  Markings.residual_surjective B₀ f (SourceTorus.toCommonTori_surjective H K₀ hK e S hn hmodel)
    (commonTori_odd H K₀ e S hn hmodel)

/-- Actual conjugation on B, using characteristicity of its defining residual. -/
noncomputable def residualAction (g : normalizer (B₀ : Set G)) :
    MulAut (residualBorel H K₀ hK S) :=
  (residualBorel H K₀ hK S).normalizerMonoidHom
    ⟨g.val, normalizer_le_residual_normalizer B₀ g.property⟩

omit [Finite G] in
theorem residualAction_apply (g : normalizer (B₀ : Set G)) (b : residualBorel H K₀ hK S) :
    (residualAction H K₀ hK S g b : G) = g.val * b.val * g.val⁻¹ := rfl

/-- The residual surjection is equivariant for the original normalizer action. -/
theorem residualMap_equivariant (g : normalizer (B₀ : Set G)) (b : residualBorel H K₀ hK S) :
    residualMap H K₀ hK e S hn hmodel (residualAction H K₀ hK S g b) =
      SourceTorus.normalizerAction H K₀ hK e S hn hmodel g
        (residualMap H K₀ hK e S hn hmodel b) :=
  (SourceTorus.normalizerAction_toCommonTori H K₀ hK e S hn hmodel g
    (inclusion (map_subtype_le (pResidual 2 B₀)) b)).symm

/-- A prime restriction on the actual [B,s] transfers to the torus displacement. -/
theorem displacement_primes (g : normalizer (B₀ : Set G)) (P : ℕ → Prop)
    (hP : ∀ p : ℕ, p.Prime →
      p ∣ Nat.card (⁅residualBorel H K₀ hK S, zpowers g.val⁆ : Subgroup G) → P p) :
    ∀ p : ℕ, p.Prime →
      p ∣ Nat.card (CartanAction.displacement
        (SourceTorus.normalizerAction H K₀ hK e S hn hmodel g)) → P p :=
  CartanAction.displacement_prime_restriction_of_commutator
    (residualBorel H K₀ hK S) g.val (residualAction H K₀ hK S g)
    (residualAction_apply H K₀ hK S g)
    (SourceTorus.normalizerAction H K₀ hK e S hn hmodel g)
    (residualMap H K₀ hK e S hn hmodel) (residualMap_surjective H K₀ hK e S hn hmodel)
    (residualMap_equivariant H K₀ hK e S hn hmodel g) P hP

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions
variable {G : Type*} [Group G] [Finite G]
variable (H K T : Subgroup G) (hTH : T ≤ H) {t : G} (ht : t ∈ T)
variable (hK : K ⊔ K.conjBy t ≤ H)
variable (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
variable (htn : t ∉ normalizer (K : Set G))
variable (e : Source.starImage H (K ⊔ K.conjBy t) ≃*
  Source.starImage H K × Source.starImage H K)
variable (he : ∀ a b, (e.symm (a, b) : Source.Hstar H) = (a : Source.Hstar H) *
  (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩ * b *
    (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩)⁻¹))
variable (S : Sylow 2 (Source.starImage H (K ⊔ K.conjBy t)))
variable {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
local notation "B₀" => SourceTorus.chosenLift H (K ⊔ K.conjBy t) hK S
local notation "C" => CommonTorus H (K ⊔ K.conjBy t) e S

include hi htn he in
/-- The moving source element exchanges the torus axes; every element of T
preserves both or exchanges both. All product and torus identities are derived. -/
theorem source_factor_actions (hTB : T ≤ normalizer (B₀ : Set G)) :
    CartanAction.ExchangesFactors
      (SourceTorus.normalizerAction H (K ⊔ K.conjBy t) hK e S hn hmodel ⟨t, hTB ht⟩) ∧
    ∀ s : T, CartanAction.PreservesFactors
        (SourceTorus.normalizerAction H (K ⊔ K.conjBy t) hK e S hn hmodel ⟨s.val, hTB s.property⟩) ∨
      CartanAction.ExchangesFactors
        (SourceTorus.normalizerAction H (K ⊔ K.conjBy t) hK e S hn hmodel ⟨s.val, hTB s.property⟩) := by
  have hnorm := normalizes_orbit H K (le_sup_left.trans hK) hi (hTH ht) htn
  constructor
  · obtain ⟨h₁, h₂⟩ := binary_moving_exchanges H K (hTH ht) hK hi htn e he S
      (hnorm (hTH ht)) (hTB ht)
    exact normalizerAction_exchanges H _ hK e S hn hmodel (hTH ht) (hnorm (hTH ht)) (hTB ht) h₁ h₂
  · intro s
    rcases binary_permutation H K (hTH ht) hK hi htn e he S
      (hTH s.property) (hnorm (hTH s.property)) (hTB s.property) with h | h
    · exact Or.inl (normalizerAction_preserves H _ hK e S hn hmodel
        (hTH s.property) (hnorm (hTH s.property)) (hTB s.property) h.1 h.2)
    · exact Or.inr (normalizerAction_exchanges H _ hK e S hn hmodel
        (hTH s.property) (hnorm (hTH s.property)) (hTB s.property) h.1 h.2)

include hi htn he in
/-- The complete conditional marked-action data for CartanAction.three_power_of_markings.
The commutator prime bound transfers by displacement_primes above. The final
parameter, residual equality and full projected-image assembly remain with 13.8.16. -/
theorem source_actions (L V₁ : Subgroup G)
    (hLB : one L T V₁ ≤ B₀)
    (hzero : zero L ≤ one L T V₁) (hplus : plus L T V₁ ≤ one L T V₁)
    (hTB : T ≤ normalizer (B₀ : Set G))
    (hTzero : T ≤ normalizer (zero L : Set G))
    (hTplus : T ≤ normalizer (plus L T V₁ : Set G))
    (hc₀ : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hcplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    {s : G} (hs : s ∈ T ⊓ L)
    (hinv : ∀ u : plus L T V₁ ⧸ pCore 2 (plus L T V₁),
      coreAction (plus L T V₁) ⟨s, hTplus hs.1⟩ u = u⁻¹) :
    let τ := SourceTorus.normalizerAction H (K ⊔ K.conjBy t) hK e S hn hmodel ⟨t, hTB ht⟩
    let α := SourceTorus.normalizerAction H (K ⊔ K.conjBy t) hK e S hn hmodel ⟨s, hTB hs.1⟩
    let Z := D₀ H (K ⊔ K.conjBy t) hK e S hn hmodel L
    let P := Dplus H (K ⊔ K.conjBy t) hK e S hn hmodel L T V₁
    IsCyclic C ∧ Odd (Nat.card C) ∧
    CartanAction.ExchangesFactors τ ∧
    (CartanAction.PreservesFactors α ∨ CartanAction.ExchangesFactors α) ∧
    Nat.card Z = 3 ∧ Nat.card P = 3 ∧
    Z.map τ.toMonoidHom = Z ∧ P.map τ.toMonoidHom = P ∧
    (∀ z ∈ Z, α z = z) ∧ (∀ z ∈ P, α z = z⁻¹) := by
  obtain ⟨hτ, hα⟩ := source_factor_actions H K T hTH ht hK hi htn e he S hn hmodel hTB
  refine ⟨BinaryBorel.torus_cyclic hn hmodel _, commonTorus_odd H _ e S hn hmodel,
    hτ, hα ⟨s, hs.1⟩, ?_⟩
  exact marked_actions H _ hK e S hn hmodel L T V₁ hLB hzero hplus hTB hTzero hTplus
    hc₀ hcplus ht hs hinv

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions

end
