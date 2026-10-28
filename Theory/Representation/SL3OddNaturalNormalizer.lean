module

public import Theory.Representation.SL3OddNaturalNormalizer.Index
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Odd index of the binary natural SL₃ normalizer

For a finite binary field F of order 2^m, the natural SL₃ image S in the
binary general linear group has index dividing `(2^m - 1) * m` in its
actual normalizer N. Consequently `[N : S]` is odd when m is positive and
odd, and every two-subgroup of N lies in S. The field F₂ is included.

The proof constructs the faithful identification of S inside N with the
special linear matrix group, using the literal restriction of scalars of
`specialLinearNatural 3`. The imported index theorem obtains semilinearity
from the additive scalar centralizer and uses the field-automorphism and
determinant homomorphisms; no normalizer coverage is assumed.

This supplies the intrinsic natural-three model estimate for
Aschbacher–Smith, *The Classification of Quasithin Groups*, B.5.9(4) and
B.5.10(2), printed pp.107–109 of the combined manuscript (1 March 2004).
The action-image transport and the product decomposition remain with the
Chapter B consumer in `ProductGeometry.Localization`. Its specified normal
component and natural action also fit `two_subgroup_le_of_natural` directly.
-/

@[expose] public section
noncomputable section
namespace Representation.SL3OddNaturalNormalizer
variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

/-- The actual natural SL₃ representation restricted to the binary field. -/
def binaryNatural : Representation (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin 3) F) (Fin 3 → F) :=
  restrictScalars (k := ZMod 2) (specialLinearNatural 3)

/-- The concrete binary general linear group of the natural space. -/
abbrev BinaryGL := (Module.End (ZMod 2) (Fin 3 → F))ˣ

/-- The image of the actual natural representation in the binary linear group. -/
def naturalImage : Subgroup (BinaryGL F) := (binaryNatural F).asGroupHom.range

/-- The full normalizer in the binary general linear group. -/
def normalizer : Subgroup (BinaryGL F) := Subgroup.normalizer (naturalImage F : Set (BinaryGL F))

/-- Normality is relative to the full normalizer. -/
instance naturalImage_normal : ((naturalImage F).subgroupOf (normalizer F)).Normal :=
  inferInstanceAs ((naturalImage F).subgroupOf
    (Subgroup.normalizer (naturalImage F : Set (BinaryGL F)))).Normal

/-- The faithful action of the actual normalizer on the same vector space. -/
def normalizerRepresentation : Representation (ZMod 2) (normalizer F) (Fin 3 → F) :=
  (Units.coeHom _).comp (normalizer F).subtype

theorem binaryNatural_injective : Function.Injective (binaryNatural F) := by
  intro g h he
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun he v

theorem binaryNatural_asGroupHom_injective : Function.Injective (binaryNatural F).asGroupHom := by
  intro g h he
  exact binaryNatural_injective F (congrArg Units.val he)

theorem normalizerRepresentation_injective : Function.Injective (normalizerRepresentation F) := by
  intro g h he
  exact Subtype.ext (Units.ext he)

/-- The actual natural image, regarded inside its normalizer, is SL₃ via the
faithful natural matrix action. -/
def normalizerImageEquiv :
    (naturalImage F).subgroupOf (normalizer F) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
  (Subgroup.subgroupOfEquivOfLe (naturalImage F).le_normalizer).trans
    (MonoidHom.ofInjective (binaryNatural_asGroupHom_injective F)).symm

/-- The marked isomorphism has exactly the natural action on column vectors. -/
theorem normalizerRepresentation_natural
    (g : (naturalImage F).subgroupOf (normalizer F)) (v : Fin 3 → F) :
    normalizerRepresentation F (g : normalizer F) v =
      Matrix.mulVec (normalizerImageEquiv F g).val v := by
  have he := MonoidHom.apply_ofInjective_symm (binaryNatural_asGroupHom_injective F)
    (Subgroup.subgroupOfEquivOfLe (naturalImage F).le_normalizer g)
  exact (congrArg (fun u : BinaryGL F => (u : Module.End (ZMod 2) (Fin 3 → F)) v) he).symm

variable [Finite F]

/-- The normalizer quotient has order dividing `(2^m - 1) * m`. -/
theorem normalizer_relIndex_dvd {m : ℕ} (hc : Nat.card F = 2 ^ m) :
    (naturalImage F).relIndex (normalizer F) ∣ (2 ^ m - 1) * m :=
  index_dvd_field_units_mul_degree hc ((naturalImage F).subgroupOf (normalizer F))
    (normalizerImageEquiv F) (normalizerRepresentation F)
    (normalizerRepresentation_injective F) (normalizerRepresentation_natural F)

/-- For positive odd binary field degree the natural SL₃ image has odd index
in its full binary linear normalizer, including the field with two elements. -/
theorem odd_normalizer_relIndex {m : ℕ} (hm : 0 < m) (hodd : Odd m)
    (hc : Nat.card F = 2 ^ m) :
    Odd ((naturalImage F).relIndex (normalizer F)) :=
  odd_index_of_natural hm hodd hc ((naturalImage F).subgroupOf (normalizer F))
    (normalizerImageEquiv F) (normalizerRepresentation F)
    (normalizerRepresentation_injective F) (normalizerRepresentation_natural F)

/-- Every two-subgroup normalizing the actual natural image is contained in
that image. This is the intrinsic model input to natural-three localization. -/
theorem two_subgroup_le_naturalImage {m : ℕ} (hm : 0 < m) (hodd : Odd m)
    (hc : Nat.card F = 2 ^ m) (A : Subgroup (BinaryGL F)) (hA : IsPGroup 2 A)
    (hAN : A ≤ normalizer F) : A ≤ naturalImage F := by
  have hle := two_subgroup_le_of_natural hm hodd hc
    ((naturalImage F).subgroupOf (normalizer F))
    (normalizerImageEquiv F) (normalizerRepresentation F)
    (normalizerRepresentation_injective F) (normalizerRepresentation_natural F)
    (A.subgroupOf (normalizer F)) hA.comap_subtype
  intro a ha
  exact hle (show (⟨a, hAN ha⟩ : normalizer F) ∈ A.subgroupOf (normalizer F) from ha)

end Representation.SL3OddNaturalNormalizer
