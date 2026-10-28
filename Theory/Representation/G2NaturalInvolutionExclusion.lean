module

public import Theory.Representation.G2.NaturalInvolutionRank
public import Theory.Representation.G2NaturalNormalizerOffenders
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Involution displacement in the full binary natural G₂ normalizer

Over a field of order 2^n, every nonidentity involution in the full binary
linear normalizer of the natural G₂ module moves at least 2n dimensions.
An inner involution moves at least two field dimensions. A nontrivial field
involution moves exactly half the binary space, namely 3n dimensions; the
normalizer theorem constructs its scalar and field factors. The bound is
transported to any faithful ambient action with the marked normal component.

This excludes the ordinary G₂(2^n) branch, n > 1, for the original involution
of displacement rank at most two in the Chapter 13 module classification.
Source: Aschbacher–Smith B.4.6, K.3 and 13.5.21, printed pp.88–90,457,923–924;
Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5.
-/

public noncomputable section

namespace Atlas.G2.Natural.Normalizer
open Representation Representation.BinaryOffender Subgroup
attribute [local instance] ZMod.algebra
variable (F : Type*) [Field F] [CharP F 2] [Finite F]

/-- Restricting scalars multiplies the natural no-transvection bound by n. -/
theorem binary_involution_displacement_ge {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (g : Model F) (hg : g ≠ 1) (hg2 : g ^ 2 = 1) :
    2 * n ≤ Module.finrank (ZMod 2) ((binary F g - 1).range) := by
  have hr := InvolutionRank.two_le_operatorFixedCodim_of_involution g hg
    (by simpa only [pow_two] using hg2)
  have hd : Module.finrank (ZMod 2) F = n := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hF
  rw [binary_apply]
  change 2 * n ≤ Module.finrank (ZMod 2)
    (((Natural.action F g - 1).restrictScalars (ZMod 2)).range)
  rw [LinearMap.range_restrictScalars,
    ((Natural.action F g - 1).range.restrictScalarsEquiv (ZMod 2)).restrictScalars
      (ZMod 2) |>.finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) F, hd]
  simpa only [NaturalTensor.operatorFixedCodim, Nat.mul_comm n 2] using
    Nat.mul_le_mul_left n hr

/-- Every involution in the full binary normalizer moves at least 2n dimensions. -/
theorem normalizer_involution_displacement_ge {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (t : linearNormalizer (binary F)) (ht : orderOf t = 2) :
    2 * n ≤ Module.finrank (ZMod 2)
      ((normalizerRepresentation (binary F) t - 1).range) := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  obtain ⟨z, hz⟩ := LieAutomorphismExtensions.semilinearAction_surjective hq
    (normalizerAutomorphism F t)
  by_cases hs : z.right = 1
  · obtain ⟨g, rfl⟩ := inner_involution_mem F hq t ht2 z hz hs
    have hi : Function.Injective (normalizerEmbedding (binary F)) := by
      intro a b h
      exact binary_faithful F (congrArg (fun x : linearNormalizer (binary F) => x.val.val) h)
    have hg : g ≠ 1 := by
      intro he
      apply ht1
      simp only [he, map_one]
    have hg2 : g ^ 2 = 1 := hi (by simpa only [map_pow, map_one] using ht2)
    exact binary_involution_displacement_ge F hF g hg hg2
  · have hd := field_involution_codim F hq hF t ht2 z hz hs
    rw [fixedCodim_zpowers_eq_displacement_rank] at hd
    change Module.finrank (ZMod 2)
      ((normalizerRepresentation (binary F) t - 1).range) = 3 * n at hd
    omega

/-- The same bound for the original ambient involution and actual component action. -/
theorem ambient_involution_displacement_ge {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W)
    (H : Subgroup G) [H.Normal] (e : H ≃* Model F)
    (E : W ≃ₗ[ZMod 2] Space F)
    (hE : ∀ (h : H) v, E (ρ h v) = Natural.action F (e h) (E v))
    (hf : Function.Injective ρ) {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (t : G) (ht : orderOf t = 2) :
    2 * n ≤ Module.finrank (ZMod 2) ((ρ t - 1).range) := by
  let τ : Representation (ZMod 2) G (Space F) := E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (g : G) (v : W) : E (ρ g v) = τ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hnat (h : H) : τ.asGroupHom h = (binary F).asGroupHom (e h) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change E (ρ h (E.symm v)) = binary F (e h) v
    rw [binary_apply]
    rw [hE, E.apply_symm_apply]
    simp only [LinearMap.restrictScalars_apply]
  have himage : actionImage (τ.comp H.subtype) = actionImage (binary F) := by
    ext a
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨e h, Units.ext (congrArg Units.val (hnat h).symm)⟩
    · rintro ⟨g, rfl⟩
      refine ⟨e.symm g, Units.ext ?_⟩
      simpa only [e.apply_symm_apply, Representation.asGroupHom_apply,
        MonoidHom.comp_apply, Subgroup.coe_subtype] using congrArg Units.val (hnat (e.symm g))
  let k : G →* linearNormalizer (binary F) := τ.asGroupHom.codRestrict _ (fun g => by
    change τ.asGroupHom g ∈ normalizer (actionImage (binary F) : Set _)
    rw [← himage]
    exact actionImage_le_linearNormalizer τ H ⟨g, rfl⟩)
  have hk : Function.Injective k := by
    intro a b hab
    apply hf
    apply E.conjRingEquiv.injective
    exact congrArg (fun x : linearNormalizer (binary F) => x.val.val) hab
  have hkt : orderOf (k t) = 2 := (orderOf_injective k hk t).trans ht
  have hr := normalizer_involution_displacement_ge F hn hF (k t) hkt
  have hd := NaturalTensor.operatorFixedCodim_eq_of_equiv (ρ t)
    (normalizerRepresentation (binary F) (k t)) E (hτ t)
  change Module.finrank (ZMod 2) ((ρ t - 1).range) =
    Module.finrank (ZMod 2) ((normalizerRepresentation (binary F) (k t) - 1).range) at hd
  rw [hd]
  exact hr

end Atlas.G2.Natural.Normalizer
