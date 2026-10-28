module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointRecognition
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.SourceAssembly

/-!
# Assembly of the G₂ cubic degree estimates

The concrete tensor classification and Frobenius descent leave only the natural
and adjoint actions below degree `18*r`. A tensor/outer-action estimate gives
that window; a common-fixed-space estimate excludes the actual adjoint action.
The resulting strict `14*r` bound feeds the existing marked source consumer.

The two estimates remain explicit premises here. This is a conditional
assembly, not a proof of GM04 Theorem 8.1 or of K.3.5. The binary derived
endpoint also still needs its independent fixed-space calculation.

Source: Aschbacher–Smith, printed p.457/PDF p.468; Guralnick–Malle,
Classification of 2F-modules II, Proposition 8.2 and Lemma 8.5, pp.53–56
of the author manuscript. See `G2CubicDegree/Source.md` for the exact scope.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
attribute [local instance] ZMod.algebra

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The tensor window and adjoint fixed-space calculation suffice for the
strict degree bound. Both still require their independent mathematical proofs. -/
theorem degree_lt_of_cubic_estimates
    (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible σ]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ) (hc : cubicRatio (normalizerRepresentation σ) ≤ 2)
    (hwindow : ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A →
      Module.finrank (ZMod 2) V < 18 * r)
    (hadjoint : Quasiequivalent σ (adjointBinary F) →
      ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      2 * rank A < fixedCodim (normalizerRepresentation σ) A) :
    Module.finrank (ZMod 2) V < 14 * r := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨A, hA, hcube, hsmall⟩ :=
    (cubicRatio_le_nat_iff (normalizerRepresentation σ) 2).mp hc
  rcases natural_or_adjoint_or_large σ hr hF hf with hn | ha | hl
  · obtain ⟨_, e, _⟩ := hn
    have hd := e.finrank_eq.trans (naturalBinary_degree F hF)
    omega
  · exact ((not_lt_of_ge hsmall) (hadjoint ha A hA hcube)).elim
  · exact ((not_lt_of_ge hl) (hwindow A hA hcube hsmall)).elim

/-- Application to the literal original component and its ambient cubic actor.
The cover marking and natural intertwiner are those of the existing consumer. -/
theorem marked_natural_of_cubic_estimates
    {G : Type*} [Group G] [Finite G] (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (e : L ≃* Atlas.G2.Model F) (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2)
    (hwindow : ∀ σ : Representation (ZMod 2) (Atlas.G2.Model F) V,
      IsIrreducible σ → Function.Injective σ → ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A →
      Module.finrank (ZMod 2) V < 18 * r)
    (hadjoint : ∀ σ : Representation (ZMod 2) (Atlas.G2.Model F) V,
      IsIrreducible σ → Function.Injective σ → Quasiequivalent σ (adjointBinary F) →
      ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      2 * rank A < fixedCodim (normalizerRepresentation σ) A) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model F),
      ∃ f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space F,
        ∀ g : L, ∀ v, f (ρ g v) = derivedNaturalBinary F (e' g) (f v) := by
  apply g2_natural_of_normalizer_degree_bound ρ L hr hF e hf hc
  intro σ hi hfaith hcube
  let : IsIrreducible σ := hi
  exact degree_lt_of_cubic_estimates σ hr hF hfaith hcube
    (hwindow σ hi hfaith) (hadjoint σ hi hfaith)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
