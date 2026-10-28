module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.BinaryDegree
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsReduction

/-!
# Applications of the exceptional GM04 representation inputs

The group-only cover producers supply the equivalences below. The original
faithful action embeds in the full linear normalizer of its irreducible
component. A numerical G₂ degree estimate then gives the actual natural
module, via the proved tensor and binary permutation catalogues. For Tits,
a pointwise cubic displacement bound contradicts the transported actor.

The three representation estimates are explicit premises of these helpers.
Their independent producers must discharge them before this is the source
classification. In particular no SQTK property of the linear normalizer is
assumed. The original SQTK and generalized-Fitting hypotheses can be retained
by those producers if their proof needs the smaller source domain.

Source: Aschbacher--Smith K.3, printed p.457, citing Guralnick--Malle,
Classification of 2F-modules II, Theorem 8.1 and Table 17.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.Exceptional
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
attribute [local instance] ZMod.algebra

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
  [IsIrreducible (ρ.comp L.subtype)]

/-- Apply the nonbinary numerical producer to the literal component action.
The conclusion retains the actual derived group and module intertwiner. -/
theorem g2_natural_of_normalizer_degree_bound
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (e : L ≃* Atlas.G2.Model F) (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2)
    (hdegree : ∀ σ : Representation (ZMod 2) (Atlas.G2.Model F) V,
      IsIrreducible σ → Function.Injective σ →
      cubicRatio (normalizerRepresentation σ) ≤ 2 → Module.finrank (ZMod 2) V < 14 * r) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model F),
      ∃ f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space F,
        ∀ g : L, ∀ v, f (ρ g v) = derivedNaturalBinary F (e' g) (f v) := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  have hi : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective (ρ.comp L.subtype)).mpr inferInstance
  exact g2_marked_natural_of_degree_lt ρ L hr hF e hf
    (hdegree σ hi (hf.comp (L.subtype_injective.comp e.symm.injective))
      (cubicRatio_model_normalizer_le_two ρ L e.symm hf hc))

attribute [local instance] BinarySix.scalars

/-- The numerical producer at r=1 feeds the separate derived-group
permutation catalogue; the full nonsimple G₂(2) is not substituted. -/
theorem g2_binary_natural_of_normalizer_degree_bound
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2)
    (hdegree : ∀ σ : Representation (ZMod 2) (commutator (Atlas.G2.Model (ZMod 2))) V,
      IsIrreducible σ → Function.Injective σ →
      cubicRatio (normalizerRepresentation σ) ≤ 2 → Module.finrank (ZMod 2) V ≤ 8) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model (ZMod 2)),
      ∃ f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2),
        ∀ g : L, ∀ v, f (ρ g v) = derivedNaturalBinary (ZMod 2) (e' g) (f v) := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  have hi : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective (ρ.comp L.subtype)).mpr inferInstance
  exact g2_binary_marked_natural_of_degree_le_eight ρ L e hf
    (hdegree σ hi (hf.comp (L.subtype_injective.comp e.symm.injective))
      (cubicRatio_model_normalizer_le_two ρ L e.symm hf hc))

/-- The pointwise GM04 Tits estimate applies to the transported original
actor and contradicts its ratio. The estimate remains an explicit input. -/
theorem tits_exclusion_of_cubic_displacement_bound
    (e : L ≃* Tits.ParrottGroup) (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2)
    (hdisplacement : ∀ σ : Representation (ZMod 2) Tits.ParrottGroup V,
      IsIrreducible σ → Function.Injective σ →
      ∀ A : Subgroup (linearNormalizer σ),
        IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
          2 * rank A < fixedCodim (normalizerRepresentation σ) A) : False := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  have hi : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective (ρ.comp L.subtype)).mpr inferInstance
  obtain ⟨A, hA, hcube, hcodim⟩ := (cubicRatio_le_nat_iff (normalizerRepresentation σ) 2).mp
    (cubicRatio_model_normalizer_le_two ρ L e.symm hf hc)
  exact (not_lt_of_ge hcodim)
    (hdisplacement σ hi (hf.comp (L.subtype_injective.comp e.symm.injective)) A hA hcube)

end CFSG.Quasithin.ChapterK.Exceptional
