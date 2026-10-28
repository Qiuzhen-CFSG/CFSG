module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.SmallDerivedCovers.Source
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.SourceAssembly
public import Theory.Representation.NormalPSubgroupKernel

/-!
# The two small-derived covering identifications in Chapter K

These applications start with the central quotient of the original normal
perfect subgroup and its faithful irreducible binary action. The action
kills its two-core, discharging the remaining group-theoretic hypothesis
of the G₂(2)′ identification. The Tits identification needs no core premise.
The resulting equivalences feed the existing K.3 representation consumers.

Only the independent G₂ degree estimate and Tits displacement estimate
remain explicit. Their proofs and the final module/action/ratio conclusions
belong to the exceptional-family assembly. No SQTK property of a full linear
normalizer is assumed here.

Source: Aschbacher–Smith K.3, printed p.457. The covering step uses I.1.3;
the separate representation step cites Guralnick–Malle II, Theorem 8.1,
Table 17 and Lemmas 8.5, 8.8 (the binary G₂ case refers to Part I, §4).
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition

attribute [local instance] ZMod.algebra BinarySix.scalars

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
  [Group.IsPerfect L] [IsIrreducible (ρ.comp L.subtype)]

/-- The source binary action discharges the two-core condition. Its actual
central quotient marking then supplies the K.3 natural-module consumer;
only the independent representation degree estimate remains. -/
theorem g2_binary_natural_of_centralQuotient_and_degree_bound
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2)
    (hdegree : ∀ σ : Representation (ZMod 2) (commutator (Atlas.G2.Model (ZMod 2))) V,
      IsIrreducible σ → Function.Injective σ →
      cubicRatio (normalizerRepresentation σ) ≤ 2 → Module.finrank (ZMod 2) V ≤ 8) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model (ZMod 2)),
      ∃ f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2),
        ∀ g : L, ∀ v, f (ρ g v) = derivedNaturalBinary (ZMod 2) (e' g) (f v) := by
  have hfaith : Function.Injective (ρ.comp L.subtype) := hf.comp L.subtype_injective
  have hcore : pCore 2 L = ⊥ := by
    exact le_bot_iff.mp ((normal_p_subgroup_le_ker (ρ.comp L.subtype) (pCore 2 L)
      (pCore_isPGroup (p := 2))).trans ((MonoidHom.ker_eq_bot_iff _).mpr hfaith).le)
  exact ChapterK.Exceptional.g2_binary_natural_of_normalizer_degree_bound ρ L
    (g2DerivedEquivOfTwoCoreEqBot hcore e) hf hc hdegree

/-- The actual Tits central quotient feeds the original-action exclusion.
The independent displacement estimate is explicit; no covering or lifted
relation premise remains. -/
theorem tits_exclusion_of_centralQuotient_and_displacement_bound
    (e : L ⧸ center L ≃* Tits.ParrottGroup)
    (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2)
    (hdisplacement : ∀ σ : Representation (ZMod 2) Tits.ParrottGroup V,
      IsIrreducible σ → Function.Injective σ →
      ∀ A : Subgroup (linearNormalizer σ),
        IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
          2 * rank A < fixedCodim (normalizerRepresentation σ) A) : False :=
  ChapterK.Exceptional.tits_exclusion_of_cubic_displacement_bound ρ L
    (titsEquiv e) hf hc hdisplacement

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional
