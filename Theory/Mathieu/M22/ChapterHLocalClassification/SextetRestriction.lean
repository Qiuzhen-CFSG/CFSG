module

public import Theory.Mathieu.M24.ChapterHStabilizers.SextetAction
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure

/-!
# The source-marked sextet core and its pair restrictions

Conjugation by the certified native word carrying the standard sextet onto
`m22SourceSextet` transports its intrinsic E64 core and its genuine hexacode
conjugation action. Restrict this core to the native pointwise and setwise
pair groups to define the inner and outer translation candidates. These
candidates lie in the intrinsic quintet two-cores; the reverse containments,
their orders, and the local quotient and module identifications are subsequent
classification obligations.

The shared candidates separate those group/action calculations from the
compatible Sylow elementary catalogue. Both branches use the literal pair
{0,9} and the same source geometry, and the inclusion into the pair group
identifies the inner candidate with the inner intersection of the outer one.

Source: Aschbacher--Smith H.14.3 and its proof, printed p.397, combined
manuscript of 1 March 2004. The transported hexacode calculation is the licensed
ATLAS port cited in `M24.ChapterHStabilizers.SextetAction`; no new port is used.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode
open scoped Pointwise
namespace Sporadic.Mathieu.M22ChapterH.Sextet

/-- Conjugation from the standard to the pair-compatible source sextet. -/
def sourceStabilizerEquiv :
    sextetStabilizer standardSextet ≃* sextetStabilizer m22SourceSextet :=
  MulAction.stabilizerEquivStabilizer m22SourceSextet_eq_smul

@[simp] theorem sourceStabilizerEquiv_coe (g : sextetStabilizer standardSextet) :
    (sourceStabilizerEquiv g).val = MulAut.conj m22GeometryConjugator g.val :=
  MulAction.stabilizerEquivStabilizer_apply m22SourceSextet_eq_smul g

/-- The intrinsic source sextet core, included in M24. -/
def sourceCore : Subgroup M24 :=
  (pCore 2 (sextetStabilizer m22SourceSextet)).map (sextetStabilizer m22SourceSextet).subtype

theorem sourceCore_eq_conjugate :
    sourceCore = SextetCore.core.map (MulAut.conj m22GeometryConjugator).toMonoidHom := by
  have he : (sextetStabilizer m22SourceSextet).subtype.comp sourceStabilizerEquiv.toMonoidHom =
      (MulAut.conj m22GeometryConjugator).toMonoidHom.comp
        (sextetStabilizer standardSextet).subtype := by
    apply MonoidHom.ext
    intro g
    exact sourceStabilizerEquiv_coe g
  rw [sourceCore, ← pCore_map_iso 2 sourceStabilizerEquiv, Subgroup.map_map, he,
    ← Subgroup.map_map]
  rfl

theorem sourceCore_elementary : IsElementaryAbelian 2 sourceCore := by
  rw [sourceCore_eq_conjugate]
  let := SextetCore.core_ambient_elementary
  exact IsElementaryAbelian.map _

theorem sourceCore_card : Nat.card sourceCore = 64 := by
  rw [sourceCore_eq_conjugate]
  exact (Subgroup.card_map_of_injective (K := SextetCore.core)
    (f := (MulAut.conj m22GeometryConjugator).toMonoidHom)
    (MulAut.conj m22GeometryConjugator).injective).trans SextetCore.core_ambient_card

/-- Native hexacode translation coordinates in the source sextet core. -/
def sourceTranslationEquiv : Multiplicative Atlas.Codes.hexacode ≃* sourceCore :=
  M24ChapterHStabilizers.SextetAction.ambientTranslationEquiv.trans
    (((MulAut.conj m22GeometryConjugator).subgroupMap SextetCore.core).trans
      (MulEquiv.subgroupCongr sourceCore_eq_conjugate.symm))

@[simp] theorem sourceTranslationEquiv_coe (v : Multiplicative Atlas.Codes.hexacode) :
    (sourceTranslationEquiv v).val = MulAut.conj m22GeometryConjugator
      (M24ChapterHStabilizers.SextetAction.ambientTranslationEquiv v).val := rfl

/-- The full literal source-stabilizer action under those same coordinates. -/
theorem sourceTranslationEquiv_conjugation (g : sextetStabilizer m22SourceSextet)
    (v : Atlas.Codes.hexacode) :
    g.val * (sourceTranslationEquiv (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (sourceTranslationEquiv (Multiplicative.ofAdd
        (Representation.Hexacode.action
          (SextetCore.quotientHom (sourceStabilizerEquiv.symm g)) v))).val := by
  obtain ⟨g, rfl⟩ := sourceStabilizerEquiv.surjective g
  rw [sourceStabilizerEquiv.symm_apply_apply, sourceStabilizerEquiv_coe,
    sourceTranslationEquiv_coe, sourceTranslationEquiv_coe, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (MulAut.conj m22GeometryConjugator)
    (M24ChapterHStabilizers.SextetAction.ambientTranslationEquiv_conjugation g v)

/-- Source sextet translations fixing both deleted coordinates. -/
def innerTranslations : Subgroup M22 := sourceCore.comap m22Embedding

/-- Source sextet translations preserving the deleted pair setwise. -/
def outerTranslations : Subgroup m22PairStabilizer := sourceCore.comap m22PairStabilizer.subtype

/-- The faithful native inclusion retains the literal inner intersection. -/
theorem innerTranslations_map_pair :
    innerTranslations.map m22ToPairStabilizer = outerTranslations ⊓ m22ToPairStabilizer.range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y, rfl⟩
  · rintro ⟨hx, y, rfl⟩
    exact ⟨y, hx, rfl⟩

private theorem restricted_core_le {G J : Type*} [Group G] [Group J]
    (f : G →* J) (hf : Function.Injective f) (D : Subgroup J) :
    ((pCore 2 D).map D.subtype).comap f ≤
      (pCore 2 (D.comap f)).map (D.comap f).subtype := by
  let r : D.comap f →* D :=
    (f.comp (D.comap f).subtype).codRestrict _ (fun g => g.property)
  have hr : Function.Injective r := fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))
  have hp : (pCore 2 D).comap r ≤ pCore 2 (D.comap f) :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective r hr⟩
  intro g hg
  obtain ⟨x, hx, hxe⟩ := hg
  have hgs : g ∈ D.comap f := by
    change f g ∈ D
    rw [← hxe]
    exact x.property
  refine ⟨⟨g, hgs⟩, hp ?_, rfl⟩
  change r ⟨g, hgs⟩ ∈ pCore 2 D
  have he : r ⟨g, hgs⟩ = x := Subtype.ext hxe.symm
  rwa [he]

/-- The translation candidate lies in the relative inner quintet two-core. -/
theorem innerTranslations_le_core : innerTranslations ≤ m22InnerQuintetKernel m22SourceSextet :=
  restricted_core_le m22Embedding m22Embedding_injective _

/-- The translation candidate lies in the relative outer quintet two-core. -/
theorem outerTranslations_le_core : outerTranslations ≤ m22OuterQuintetKernel m22SourceSextet :=
  restricted_core_le m22PairStabilizer.subtype m22PairStabilizer.subtype_injective _

end Sporadic.Mathieu.M22ChapterH.Sextet
end
