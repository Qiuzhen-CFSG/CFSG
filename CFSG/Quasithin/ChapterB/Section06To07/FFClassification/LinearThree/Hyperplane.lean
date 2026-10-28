module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree.SourceFactorStructure
public import Theory.Representation.BinaryFullLinearRecognition.Moved
/-!
# Exclusion of the genuine B.5.6 hyperplane row

The first actual factor is SL3(2) and its original moved space has dimension
three. Faithful moved-space recognition supplies natural coordinates for the
whole normalizer action. The derived simple-component orbit then gives two
proper parabolics in its minimal-parabolic automizer, a contradiction.
The original source row supplies all marks and dimensions; no natural-module
recognition conclusion, component-orbit equality or chart is an added premise.

Source: Aschbacher–Smith, B.5.6(5) and B.6.9, pp.105 and 115–116.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The actual hyperplane source row is incompatible with minimal parabolicity. -/
theorem source_hyperplane_excluded
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (c : SourceInduction.HyperplaneCase (ρ.comp Y.subtype)) : False := by
  let := c.product.first_normal
  obtain ⟨hs,hc,he,ho⟩ := source_linearThree_factor_structure T hP Y c.first hgen
    BinaryField.two (by decide) c.firstEquiv
  let := hs
  let L := c.first.map Y.subtype
  let e := (c.first.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans c.firstEquiv
  have hm : moved (ρ.comp Y.subtype) c.first = moved ρ L := by
    have hh := subspaceCommutator_map_embedding (ρ.comp Y.subtype) ρ Y.subtype
      (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ => rfl) c.first ⊤
    simpa only [Submodule.map_id] using hh
  have hd : Module.finrank (ZMod 2) (moved ρ L) = 3 := by
    rw [← hm]
    exact c.firstDimension
  obtain ⟨eg,f,hf⟩ := BinaryFullLinearRecognition.binary_three_moved_normalizer_natural ρ L e hd
  exact component_normalizer_not_natural_three T hP hc he ho
    (BinaryFullLinearRecognition.fullMovedNormalizerSpace ρ L).toRepresentation
    BinaryField.two ⟨⟨eg,f,hf⟩⟩

/-- The original offender action cannot satisfy the hyperplane source row. -/
theorem source_offender_hyperplane_excluded
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (c : SourceInduction.HyperplaneCase (ρ.comp (offenderSubgroup ρ).subtype)) : False := by
  let := offenderSubgroup_normal ρ
  exact source_hyperplane_excluded ρ T hP _ (offender_generation T hP ρ hff hcore).2 c
end CFSG.Quasithin.ChapterB
