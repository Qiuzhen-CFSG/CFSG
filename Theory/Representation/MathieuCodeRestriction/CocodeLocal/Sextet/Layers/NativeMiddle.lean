/-
The Golay and affine sextet constructions used here are by Gerald Höhn and
ATLAS contributors, under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt. Their source modules record revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.HexacodeDual
public import Theory.Representation.RepEquiv

/-!
# Native coordinates on the sextet middle factor

The same code-preserving point marking restricts to the literal native pair
span and maps the pullback tetrad line onto its native counterpart. Descending
this restriction gives coordinates on their quotient. Affine translations
displace native pair vectors into the native tetrad line.

The hexacode representation pulled back to the native stabilizer is exactly
its conjugation action on the transported translations. Its dual is irreducible
and its kernel is precisely that translation subgroup. This makes the native
middle-factor assembly independent of intrinsic prime-core identifications.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.3(1),
printed p.400 (PDF p.411).
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.SextetLayers
open CoordinateTransport

/-- Restrict the actual cocode coordinates to the within-tetrad pair span. -/
def nativePairEquiv (S : Sextet) : atlasPairSpace ≃ₗ[ZMod 2]
    ↥(⨆ B ∈ S.parts, supportedPairSpace B) :=
  (nativeCocodeEquiv S).ofSubmodules _ _ (nativePairSpace_map S)

lemma nativePairEquiv_val (S : Sextet) (v : atlasPairSpace) :
    (nativePairEquiv S v).val = nativeCocodeEquiv S v.val := rfl

/-- The restricted coordinates carry the exact quotient denominator onto the native one. -/
lemma nativeLineInPair_map (S : Sextet) :
    atlasLineInPair.map (nativePairEquiv S).toLinearMap =
      (sextetTetradLine S).comap (⨆ B ∈ S.parts, supportedPairSpace B).subtype := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change nativeCocodeEquiv S w.val ∈ sextetTetradLine S
    rw [← nativeTetradLine_map S]
    exact ⟨w.val, hw, rfl⟩
  · intro hv
    obtain ⟨w, rfl⟩ := (nativePairEquiv S).surjective v
    refine ⟨w, ?_, rfl⟩
    change nativeCocodeEquiv S w.val ∈ sextetTetradLine S at hv
    rw [← nativeTetradLine_map S] at hv
    obtain ⟨u, hu, he⟩ := hv
    change w.val ∈ atlasTetradLine
    exact (nativeCocodeEquiv S).injective he ▸ hu

/-- Quotient coordinates induced by the same native Golay marking. -/
def nativeMiddleEquiv (S : Sextet) : AtlasMiddle ≃ₗ[ZMod 2]
    (↥(⨆ B ∈ S.parts, supportedPairSpace B) ⧸
      (sextetTetradLine S).comap (⨆ B ∈ S.parts, supportedPairSpace B).subtype) :=
  Submodule.Quotient.equiv _ _ (nativePairEquiv S) (nativeLineInPair_map S)

lemma nativeMiddleEquiv_mk (S : Sextet) (v : atlasPairSpace) :
    nativeMiddleEquiv S (atlasLineInPair.mkQ v) =
      ((sextetTetradLine S).comap (⨆ B ∈ S.parts, supportedPairSpace B).subtype).mkQ
        (nativePairEquiv S v) := rfl

/-- Native affine translations have displacement in the common tetrad line. -/
lemma nativeTranslation_displacement (S : Sextet) (t : Multiplicative Atlas.Codes.hexacode)
    {v : Cocode} (hv : v ∈ ⨆ B ∈ S.parts, supportedPairSpace B) :
    cocodeRepresentation (nativeTranslation S t).val v - v ∈ sextetTetradLine S := by
  rw [← nativePairSpace_map S] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [← nativeTetradLine_map S]
  refine ⟨_, atlasTranslation_displacement t hw, ?_⟩
  change nativeCocodeEquiv S (atlasCocodeRepresentation (Atlas.Codes.sextetTranslation t) w - w) = _
  rw [map_sub, nativeCocodeEquiv_equivariant]
  rfl

/-- The hexacode action is the conjugation action on native translations. -/
def nativeHexacodeRepresentation (S : Sextet) :
    Representation (ZMod 2) (sextetStabilizer S) Atlas.Codes.hexacode :=
  Representation.Hexacode.action.comp (nativeQuotient S)

lemma nativeHexacodeRepresentation_conjugation (S : Sextet) (g : sextetStabilizer S)
    (t : Multiplicative Atlas.Codes.hexacode) :
    g * nativeTranslation S t * g⁻¹ = nativeTranslation S
      (Multiplicative.ofAdd (nativeHexacodeRepresentation S g t.toAdd)) :=
  nativeTranslation_conjugation S g t

lemma nativeHexacodeRepresentation_apply (S : Sextet) (s : Atlas.Codes.SextetStabilizer) :
    nativeHexacodeRepresentation S (nativeStabilizerEquiv S s) =
      (Representation.Hexacode.action.comp Atlas.Codes.sextetQuotient) s := by
  change Representation.Hexacode.action (nativeQuotient S (nativeStabilizerEquiv S s)) = _
  rw [nativeQuotient_apply]
  rfl

lemma nativeHexacodeRepresentation_dual_apply (S : Sextet) (s : Atlas.Codes.SextetStabilizer) :
    (nativeHexacodeRepresentation S).dual (nativeStabilizerEquiv S s) =
      (Representation.dual (Representation.Hexacode.action.comp Atlas.Codes.sextetQuotient)) s := by
  rw [Representation.dual_apply, ← map_inv, nativeHexacodeRepresentation_apply]
  rfl

lemma nativeHexacodeRepresentation_dual_isIrreducible (S : Sextet) :
    Representation.IsIrreducible (nativeHexacodeRepresentation S).dual := by
  apply Representation.RepEquiv.irreducible_of_group_iso (nativeStabilizerEquiv S)
    (ρ := (Representation.dual (Representation.Hexacode.action.comp Atlas.Codes.sextetQuotient)))
    (fun g v => congrArg (fun f => f v) (nativeHexacodeRepresentation_dual_apply S g).symm)
  exact Representation.Hexacode.sextet_dual_isIrreducible

/-- The faithful dual hexacode action has exactly the affine translations as kernel. -/
lemma nativeHexacodeRepresentation_dual_kernel (S : Sextet) :
    (nativeHexacodeRepresentation S).dual.ker = (nativeTranslation S).range := by
  rw [← nativeQuotient_kernel]
  ext g
  change (nativeHexacodeRepresentation S).dual g = 1 ↔ nativeQuotient S g = 1
  constructor
  · intro hg
    have he : Representation.Hexacode.action (nativeQuotient S g⁻¹) = 1 := by
      apply LinearMap.ext
      intro v
      apply Module.eval_apply_injective (ZMod 2)
      apply LinearMap.ext
      intro f
      exact congrArg (fun l : Module.Dual (ZMod 2) Atlas.Codes.hexacode => l v)
        (LinearMap.congr_fun hg f)
    have hn : nativeQuotient S g⁻¹ = 1 :=
      Representation.Hexacode.action_injective (he.trans (map_one _).symm)
    simpa only [map_inv, inv_eq_one] using hn
  · intro hg
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    change f (Representation.Hexacode.action (nativeQuotient S g⁻¹) v) = f v
    rw [map_inv, hg, inv_one, map_one]
    rfl

end MathieuCode.SextetLayers
