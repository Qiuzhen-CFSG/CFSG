module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree

/-!
# Discharging the adjoint branch of the G₂ cubic degree bound

The proved adjoint obstruction supplies the exact `hadjoint` premise of
`degree_lt_of_cubic_estimates` and of its marked component application. The
group marking, linear normalizer and cubic actor are the original ones.
Only the independent tensor window and automorphism rank bound remain;
their producers and final numerical assembly belong to the parent cubic
degree task. No common-fixed-space or normalizer-geometry premise remains.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 8.2
and Lemma 8.5, manuscript pp.53–56; Aschbacher–Smith, printed p.457.
See `G2CubicDegree/Source.md`.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction
open Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
attribute [local instance] ZMod.algebra

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The strict degree consumer with its adjoint premise fully discharged.
The tensor window and Chapter 16 automorphism rank remain independent inputs. -/
theorem degree_lt_of_cubic_window
    (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible σ]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ) (hc : cubicRatio (normalizerRepresentation σ) ≤ 2)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (hwindow : ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A →
      Module.finrank (ZMod 2) V < 18 * r) :
    Module.finrank (ZMod 2) V < 14 * r :=
  degree_lt_of_cubic_estimates σ hr hF hf hc hwindow
    (quasiequivalent_cubic_obstruction σ hr hF hAut)

/-- The actual marked component application, preserving its original cover and
natural-module maps, with the adjoint branch supplied by the proved obstruction. -/
theorem marked_natural_of_cubic_window
    {G : Type*} [Group G] [Finite G] (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (e : L ≃* Atlas.G2.Model F) (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (hwindow : ∀ σ : Representation (ZMod 2) (Atlas.G2.Model F) V,
      IsIrreducible σ → Function.Injective σ → ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A →
      Module.finrank (ZMod 2) V < 18 * r) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model F),
      ∃ f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space F,
        ∀ g : L, ∀ v, f (ρ g v) = derivedNaturalBinary F (e' g) (f v) :=
  marked_natural_of_cubic_estimates ρ L hr hF e hf hc hwindow
    (fun σ _ _ => quasiequivalent_cubic_obstruction σ hr hF hAut)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction
