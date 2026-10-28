module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Translations
public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodeZeroCoordinate

/-!
# No fixed vectors in the native outer quintet translation module

In the published source hexacode coordinates, the deleted native points 0 and 9
are rows 0 and 1 of coordinate 0. Two products of the existing adjacent
transposition lifts fix that entire tetrad pointwise. Their common fixed space
on the hexacode is zero, checked on the 64 systematic inputs. Lifting these
actual automorphisms to the source sextet stabilizer gives elements of Q.
The published conjugation equation then proves that the actual outer
translation representation has no nonzero common fixed vector.

Source: Aschbacher--Smith H.14.3(2), printed p.397, combined manuscript of
1 March 2004. This uses the licensed `HexacodePoint` and `HexacodeZeroCoordinate`
ports and their existing generator/coordinate definitions, originally by
Gerald Höhn and ATLAS contributors, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the ATLAS Research and
Attribution License 1.0; see `LICENSES/ATLAS.txt`. No abstract replacement
of the native group or its action is made.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode Atlas.Codes
open scoped Pointwise
namespace Sporadic.Mathieu.M22ChapterH.Quintet
open Sextet
set_option maxRecDepth 4096

private def ca : HexAutomorphisms := hexLift 1 * hexLift 2
private def cb : HexAutomorphisms := hexLift 3 * hexLift 4
private def kernelA : hexPointKernel (hexPos 0) :=
  ⟨⟨ca, by change ca.val.perm (hexPos 0) = hexPos 0; decide +kernel⟩, by
    apply LinearEquiv.ext
    exact (by decide +kernel : ∀ u : K, ca.val.localMap (hexPos 0) u = u)⟩
private def kernelB : hexPointKernel (hexPos 0) :=
  ⟨⟨cb, by change cb.val.perm (hexPos 0) = hexPos 0; decide +kernel⟩, by
    apply LinearEquiv.ext
    exact (by decide +kernel : ∀ u : K, cb.val.localMap (hexPos 0) u = u)⟩

private theorem fixed_certificate : ∀ (x : Fin 3 → K),
    Monomial.act ca.val (systematicEncoder x) = systematicEncoder x →
    Monomial.act cb.val (systematicEncoder x) = systematicEncoder x → x = 0 := by
  decide +kernel

private theorem hex_fixed_zero (w : hexacode)
    (h : ∀ g : hexPointKernel (hexPos 0), hexAction g.val.val w = w) : w = 0 := by
  have ha := congrArg Subtype.val (h kernelA)
  have hb := congrArg Subtype.val (h kernelB)
  change Monomial.act ca.val w.val = w.val at ha
  change Monomial.act cb.val w.val = w.val at hb
  have hx := fixed_certificate (hexProjection firstThree w)
  rw [systematic_reconstruct] at hx
  have hz := hx ha hb
  apply Subtype.ext
  rw [← systematic_reconstruct w, hz, map_zero]
  rfl

private def lift (g : HexAutomorphisms) : sextetStabilizer m22SourceSextet :=
  sourceStabilizerEquiv (SextetCore.sextetEquiv.symm (sextetSection g))

private theorem conjugate_point (c g : M24) (x : Fin 24) :
    (MulAut.conj c g).val x = c.val (g.val (c.val.symm x)) := rfl

private theorem atlas_point (g : sextetStabilizer standardSextet) (x : Omega) :
    (SextetCore.sextetEquiv g).val.val x =
      atlasPointEquiv.symm (g.val.val (atlasPointEquiv x)) := rfl

private theorem atlas_inverse_point (g : SextetStabilizer) (x : Omega) :
    (SextetCore.sextetEquiv.symm g).val.val (atlasPointEquiv x) =
      atlasPointEquiv (g.val.val x) := by
  have h := atlas_point (SextetCore.sextetEquiv.symm g) x
  rw [SextetCore.sextetEquiv.apply_symm_apply] at h
  exact (atlasPointEquiv.symm_apply_eq).mp h.symm

private theorem lift_point (g : HexAutomorphisms) (x : Omega) :
    (lift g).val.val (m22GeometryConjugator.val (atlasPointEquiv x)) =
    m22GeometryConjugator.val (atlasPointEquiv ((sextetSection g).val.val x)) := by
  rw [lift, sourceStabilizerEquiv_coe, conjugate_point,
    Equiv.symm_apply_apply, atlas_inverse_point]

private theorem lift_fixed_row (g : hexPointKernel (hexPos 0)) (k : Fin 4) :
    (lift g.val.val).val.val (m22GeometryConjugator.val (atlasPointEquiv (hexPos 0,k))) =
      m22GeometryConjugator.val (atlasPointEquiv (hexPos 0,k)) := by
  rw [lift_point, sextetSection_coordinates, hexPointStabilizer_fixed]
  have he : g.val.val.val.localMap (hexPos 0) = 1 := g.property
  rw [he]
  change m22GeometryConjugator.val (atlasPointEquiv (hexPos 0, rowLabel.symm (rowLabel k))) = _
  rw [Equiv.symm_apply_apply]

private theorem marked_zero :
    m22GeometryConjugator.val (atlasPointEquiv (hexPos 0,0)) = 0 := by decide +kernel
private theorem marked_nine :
    m22GeometryConjugator.val (atlasPointEquiv (hexPos 0,1)) = 9 := by decide +kernel

private theorem lift_pair (g : hexPointKernel (hexPos 0)) :
    (lift g.val.val).val ∈ m22PairStabilizer := by
  have h0 := lift_fixed_row g 0
  have h9 := lift_fixed_row g 1
  rw [marked_zero] at h0
  rw [marked_nine] at h9
  change m22Pair.image (lift g.val.val).val.val = m22Pair
  simp only [m22Pair, Finset.image_insert, Finset.image_singleton, h0, h9]

private def actor (g : hexPointKernel (hexPos 0)) : M22Quintet.Q :=
  ⟨⟨(lift g.val.val).val, lift_pair g⟩, (lift g.val.val).property⟩

private theorem lift_quotient (g : HexAutomorphisms) :
    SextetCore.quotientHom (sourceStabilizerEquiv.symm (lift g)) = g := by
  rw [lift, sourceStabilizerEquiv.symm_apply_apply]
  change sextetQuotient (SextetCore.sextetEquiv
    (SextetCore.sextetEquiv.symm (sextetSection g))) = g
  rw [SextetCore.sextetEquiv.apply_symm_apply, sextetQuotient_section]

private theorem word_fixed_of_conjugation (g : sextetStabilizer m22SourceSextet)
    (w : hexacode)
    (h : g.val * (sourceTranslationEquiv (Multiplicative.ofAdd w)).val * g.val⁻¹ =
      (sourceTranslationEquiv (Multiplicative.ofAdd w)).val) :
    Representation.Hexacode.action (SextetCore.quotientHom (sourceStabilizerEquiv.symm g)) w = w := by
  apply Multiplicative.ofAdd.injective
  apply sourceTranslationEquiv.injective
  exact Subtype.ext ((sourceTranslationEquiv_conjugation g w).symm.trans h)

private theorem outer_action_ambient (g : M22Quintet.Q) (v : Additive outerTranslationGroup) :
    (outerTranslationConjugation g v).toMul.val.val =
      g.val.val * v.toMul.val.val * g.val.val⁻¹ := rfl

private theorem actor_coe (g : hexPointKernel (hexPos 0)) :
    (actor g).val.val = (lift g.val.val).val := rfl

/-- The literal Q-conjugation action fixes only the zero translation. -/
theorem outerTranslationConjugation_fixed_eq_zero (v : Additive outerTranslationGroup)
    (hv : ∀ g : M22Quintet.Q, outerTranslationConjugation g v = v) : v = 0 := by
  obtain ⟨u, hu⟩ := sourceTranslationEquiv.surjective
    (⟨v.toMul.val.val, v.toMul.property⟩ : sourceCore)
  have he : (sourceTranslationEquiv u).val = v.toMul.val.val := congrArg Subtype.val hu
  have hw (g : hexPointKernel (hexPos 0)) : hexAction g.val.val u.toAdd = u.toAdd := by
    have hf := congrArg (fun w : Additive outerTranslationGroup => w.toMul.val.val) (hv (actor g))
    rw [outer_action_ambient, actor_coe] at hf
    have hc : (lift g.val.val).val * (sourceTranslationEquiv u).val *
        (lift g.val.val).val⁻¹ = (sourceTranslationEquiv u).val := by
      calc
        _ = (lift g.val.val).val * v.toMul.val.val * (lift g.val.val).val⁻¹ :=
          congrArg (fun x : M24 => (lift g.val.val).val * x * (lift g.val.val).val⁻¹) he
        _ = v.toMul.val.val := hf
        _ = _ := he.symm
    have hh := word_fixed_of_conjugation (lift g.val.val) u.toAdd hc
    rw [lift_quotient] at hh
    exact hh
  have hz : u = 1 := congrArg Multiplicative.ofAdd (hex_fixed_zero u.toAdd hw)
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  change v.toMul.val.val = 1
  rw [← he, hz, map_one]
  rfl

end Sporadic.Mathieu.M22ChapterH.Quintet
