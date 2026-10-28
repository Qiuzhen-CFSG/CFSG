module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.RootReduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.PureFourCentralizer.Conjugacy
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.Identification

/-!
# Reduction to the center centralizer in the marked normalizer model

The full ambient centralizer embeds in the root normalizer. Its marked
normalizer equivalence therefore restricts to an equivalence with the
centralizer of the embedded center of the model root. The restriction retains
its literal ambient inclusion. Conjugacy then handles every pure four-group.

The source normalizer recognition and the intrinsic center-centralizer
calculation are explicit outstanding inputs. This module does not assert
either one or the unconditional pure-four centralizer theorem.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3, 46.14 and 47.6(1),
printed pp.251,257–258,264.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations.PureFourCentralizer
open InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame
open Matrix.PSL3Four
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The center of the marked root, embedded in the full normalizer model. -/
noncomputable abbrev modelCenter : Subgroup RootNormalizerModel.Model :=
  (center RootNormalizerModel.root).map RootNormalizerModel.root.subtype

/-- The independent finite-model calculation required by the source transport. -/
@[expose] def ModelCenterCentralizer : Prop :=
  Nonempty (centralizer (modelCenter : Set RootNormalizerModel.Model) ≃*
    HeisenbergFour.Model)

private theorem map_centralizer_equiv {A B : Type*} [Group A] [Group B]
    (E : Subgroup A) (f : A ≃* B) :
    (centralizer (E : Set A)).map f.toMonoidHom =
      centralizer (E.map f.toMonoidHom : Set B) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

/-- The normalizer identification carries the actual E to the embedded root center. -/
theorem map_four (P : ReturningPair D) (I : NormalizerIdentification P) :
    (P.E.subgroupOf (normalizer (P.R : Set G))).map I.equiv.toMonoidHom = modelCenter := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    change (a : G) ∈ P.E at ha
    rw [← I.E_center] at ha
    obtain ⟨r, hr, hv⟩ := ha
    refine mem_map.mpr ⟨I.rootEquiv r, (centerCongr I.rootEquiv ⟨r, hr⟩).property, ?_⟩
    change I.equiv ⟨(r : G), _⟩ = I.equiv a
    exact congrArg I.equiv (Subtype.ext hv)
  · rintro _ ⟨r, hr, rfl⟩
    let s := I.rootEquiv.symm r
    have hs : s ∈ center P.R := (centerCongr I.rootEquiv.symm ⟨r, hr⟩).property
    refine mem_map.mpr ⟨⟨(s : G), le_normalizer s.property⟩, ?_, ?_⟩
    · change (s : G) ∈ P.E
      rw [← I.E_center]
      exact mem_map_of_mem _ hs
    · exact congrArg Subtype.val (I.rootEquiv.apply_symm_apply r)

private theorem centralizer_subgroupOf (P : ReturningPair D) :
    (centralizer (P.E : Set G)).subgroupOf (normalizer (P.R : Set G)) =
      centralizer (P.E.subgroupOf (normalizer (P.R : Set G)) :
        Set (normalizer (P.R : Set G))) := by
  ext a
  constructor
  · intro ha b hb
    exact Subtype.ext (ha (b : G) hb)
  · intro ha b hb
    exact congrArg Subtype.val (ha ⟨b, le_normalizer (P.E_le_R hb)⟩ hb)

/-- Restriction of the marked normalizer equivalence to the full ambient centralizer. -/
noncomputable def centralizerCoordinates (P : ReturningPair D)
    (I : NormalizerIdentification P) :
    centralizer (P.E : Set G) ≃*
      centralizer (modelCenter : Set RootNormalizerModel.Model) :=
  (subgroupOfEquivOfLe (centralizer_le_normalizer P)).symm.trans
    ((MulEquiv.subgroupCongr (centralizer_subgroupOf P)).trans
      ((I.equiv.subgroupMap _).trans
        (MulEquiv.subgroupCongr (by
          change (centralizer (P.E.subgroupOf (normalizer (P.R : Set G)) :
            Set (normalizer (P.R : Set G)))).map I.equiv.toMonoidHom = _
          rw [map_centralizer_equiv, map_four P I]))))

/-- The restriction is exactly the normalizer map on the original ambient element. -/
theorem centralizerCoordinates_coe (P : ReturningPair D)
    (I : NormalizerIdentification P) (c : centralizer (P.E : Set G)) :
    (centralizerCoordinates P I c : RootNormalizerModel.Model) =
      I.equiv ⟨(c : G), centralizer_le_normalizer P c.property⟩ := by rfl

/-- Conditional source assembly: the normalizer and intrinsic calculation still
require their independent producers. All ambient conjugacy and restriction
premises are discharged here. -/
theorem models_of_normalizer (P : ReturningPair D) (I : NormalizerIdentification P)
    (hmodel : ModelCenterCentralizer) : PureFourCentralizerModels D := by
  intro E hE hpure
  let : IsKleinFour E := hE
  obtain ⟨g, hg⟩ := conjugate P E hpure
  let f := MulAut.conj g
  have hc : (centralizer (E : Set G)).map f.toMonoidHom =
      centralizer (P.E : Set G) := by rw [map_centralizer_equiv, hg]
  exact ⟨((f.subgroupMap _).trans (MulEquiv.subgroupCongr hc)).trans
    ((centralizerCoordinates P I).trans hmodel.some)⟩

/-- Application to the literal inner triple in 47.6(1). The separate cubic-pair
geometry and the two normalizer-model construction inputs remain explicit. -/
theorem inner_sl2Join_of_normalizer (P : ReturningPair D) (I : NormalizerIdentification P)
    (hcenter : ModelCenterCentralizer) (hgeometry : RootModelCubicGeometry)
    (Y : D.Vertex) (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (g : localCentralizer D) (hg : (g : G) ∉ actor D Y)
    (eI : intersection D Y g ≃* alternatingGroup (Fin 4)) (x : D.X) :
    sl2Join D Y ((x : G) • ((g : G) • Y)) :=
  inner_sl2Join_of_root_geometry hgeometry D (models_of_normalizer P I hcenter)
    Y hY hF hclass g hg eI x

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations.PureFourCentralizer
