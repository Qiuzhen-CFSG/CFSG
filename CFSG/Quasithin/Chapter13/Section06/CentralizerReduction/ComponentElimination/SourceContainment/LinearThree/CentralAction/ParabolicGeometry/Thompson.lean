module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Frattini
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.Setup
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FixedSpace
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.ModelOffenders
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction

/-!
# Applying the unique-offender theorem to the literal plus quotient

The earlier source data construct the normal elementary W_K inside its
actual actor and prove that J(T_v) has nontrivial image. B.2.20 then turns
a unique-offender calculation and its pointwise-centralizer condition
into both required radical equalities. Injective transport and 13.6.4
give the original Baum(T), with the same model embedding as J(T_v).

The full doubled action and its Sylow offender calculation now discharge
both representation-theoretic hypotheses. Simultaneously conjugating the
actor and the two natural summands selects a compatible marking for both
literal equalities. The source application retains full Hypothesis 13.3.1,
the actual marked A₅ configuration and genuine earlier 13.6.6, 13.6.14 and
13.6.16(3) conclusions. It constructs the full action from hypothetical
centrality. The component-normalizer lift and final central-branch
contradiction remain with the enclosing parabolic-geometry assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma B.2.20, printed p.82, and proof of 13.6.20, printed p.931.
-/

public section

open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]
    {K L T : Subgroup G} {z v : G}

/-- Apply B.2.20 after calculating the offenders and their fixed-space
centralizer. Every other hypothesis is supplied by the earlier source data.
Neither requested radical equality is an input. -/
theorem radical_images_of_unique_offender
    (e : EarlierData K L T z v)
    (d : DoubledCoordinates K L T z v e.selected.1.1 e.normalizeL e.fixSeed)
    (hunique : ∀ A : Subgroup (Gplus K L T z v e.normalizeL e.fixSeed),
      A ≤ plusImage K L T z v e.normalizeL e.fixSeed (Tv T v) →
      IsBestOffender e.plusRepresentation A → A = BinaryLinearThree.R.map (modelEmbedding d))
    (hfix : (e.internalR ⊓ centralizer (e.internalW ⊓ centralizer
      ((BinaryLinearThree.R.map (modelEmbedding d)).comap
        (plusMk K L T z v e.normalizeL e.fixSeed) : Set (plusActor K L T v)) :
          Set (plusActor K L T v))).map
            (plusMk K L T z v e.normalizeL e.fixSeed) =
              BinaryLinearThree.R.map (modelEmbedding d)) :
    plusImage K L T z v e.normalizeL e.fixSeed (elementaryAbelianMaxJ (Tv T v)) =
        BinaryLinearThree.R.map (modelEmbedding d) ∧
      plusImage K L T z v e.normalizeL e.fixSeed (ChapterB.baumann T) =
        BinaryLinearThree.R.map (modelEmbedding d) := by
  have h := ChapterB.lemma_B_2_20 e.internalW e.internalR
    (plusMk K L T z v e.normalizeL e.fixSeed)
    (plusMk_surjective K L T z v e.normalizeL e.fixSeed) e.plusMk_ker_internal
    (BinaryLinearThree.R.map (modelEmbedding d)) e.internalW_le_internalR
    e.thompson_not_le_kernel hunique hfix
  rw [e.internal_thompson_eq, e.internal_baumann_eq] at h
  exact h

omit [Finite G] in
/-- Changing both natural coordinates by g⁻¹ changes the embedded radical
by g in the original actor coordinates. -/
theorem modelEmbedding_conjugate_inverse
    {hK : K ≤ Gv v} {hL : Tv T v ≤ normalizer (Lv L v : Set G)}
    {hz : Tv T v ≤ centralizer ({z} : Set G)}
    (d : DoubledCoordinates K L T z v hK hL hz)
    (g : BinaryLinearThree.Group) :
    modelEmbedding (conjugateCoordinates d g⁻¹) =
      (modelEmbedding d).comp (MulAut.conj g).toMonoidHom := by
  ext x
  change (d.actor.symm ((MulAut.conj g⁻¹).symm x) :
    Gplus K L T z v hL hz) =
      (d.actor.symm (g * x * g⁻¹) : Gplus K L T z v hL hz)
  rw [MulAut.conj_symm_apply, inv_inv]

/-- Select one compatible actor/module marking and discharge both literal
plus-image equalities from the full doubled action. -/
theorem exists_radical_images_of_extended
    (e : EarlierData K L T z v)
    (d0 : DoubledCoordinates K L T z v e.selected.1.1 e.normalizeL e.fixSeed)
    (c : ExtendedCoordinates e d0) :
    ∃ d : DoubledCoordinates K L T z v e.selected.1.1 e.normalizeL e.fixSeed,
      plusImage K L T z v e.normalizeL e.fixSeed
        (Stellmacher.elementaryAbelianMaxJ (Tv T v)) =
          BinaryLinearThree.R.map (modelEmbedding d) ∧
      plusImage K L T z v e.normalizeL e.fixSeed (ChapterB.baumann T) =
          BinaryLinearThree.R.map (modelEmbedding d) := by
  obtain ⟨g, hAS, huniq, hfix⟩ := c.model_offenders
  let d := conjugateCoordinates d0 g⁻¹
  let A := BinaryLinearThree.R.map (modelEmbedding d)
  have hmap : A.map c.action =
      (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).map
        (BinaryLinearThree.W.prod BinaryLinearThree.W).asGroupHom := by
    change (BinaryLinearThree.R.map (modelEmbedding (conjugateCoordinates d0 g⁻¹))).map c.action = _
    rw [modelEmbedding_conjugate_inverse, map_map, map_map, ← MonoidHom.comp_assoc,
      c.on_component]
  have hAtv : A ≤ plusImage K L T z v e.normalizeL e.fixSeed (Tv T v) := by
    apply (map_le_map_iff_of_injective c.faithful).mp
    rw [hmap]
    exact hAS
  refine ⟨d, radical_images_of_unique_offender e d ?_ ?_⟩
  · intro E hE hOff
    apply map_injective c.faithful
    rw [hmap]
    exact (huniq _ (map_mono hE)).mp (c.offender_map hOff)
  · apply c.fixedCentralizer_image_eq A hAtv
    intro x hx hfx
    have hm : c.action x ∈ A.map c.action := by
      rw [hmap]
      apply (hfix _ (mem_map_of_mem c.action hx)).mp
      simpa only [hmap] using hfx
    obtain ⟨a, ha, he⟩ := hm
    exact c.faithful he ▸ ha


section Source
open A5Module
variable {M V V₁ V₂ : Subgroup G} {S : Sylow 2 G}

/-- The actual central branch: full Hypothesis 13.3.1, the marked A₅ local
configuration, and genuine earlier conclusions construct the full action.
No offender calculation, fixed-space condition, or radical image is an input. -/
theorem exists_radical_images_of_marked
    (standing : RankTwo.LocalApplication.SourceHypothesis S L)
    (f : FlagMarking S L V V₁ V₂) (localData : LocalConfiguration M f)
    (earlier : EarlierData K L (S : Subgroup G) (markedZ f.module) (markedV f.module))
    (d0 : DoubledCoordinates K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
      earlier.selected.1.1 earlier.normalizeL earlier.fixSeed)
    (hc : ⁅plusImage K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
        earlier.normalizeL earlier.fixSeed K,
      plusImage K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
        earlier.normalizeL earlier.fixSeed (Lv L (markedV f.module))⁆ = ⊥) :
    ∃ d : DoubledCoordinates K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
        earlier.selected.1.1 earlier.normalizeL earlier.fixSeed,
      plusImage K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
        earlier.normalizeL earlier.fixSeed
        (Stellmacher.elementaryAbelianMaxJ (Tv (S : Subgroup G) (markedV f.module))) =
          BinaryLinearThree.R.map (modelEmbedding d) ∧
      plusImage K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
        earlier.normalizeL earlier.fixSeed (ChapterB.baumann (S : Subgroup G)) =
          BinaryLinearThree.R.map (modelEmbedding d) := by
  obtain ⟨c⟩ := FullAction.exists_extendedCoordinates_of_marked standing f localData earlier d0 hc
  exact exists_radical_images_of_extended earlier d0 c

/-- Construct the earlier package on the marked subgroups, in particular
apply 13.6.4 to Baum(T), and identify both requested radical images. -/
theorem exists_radical_images_of_source
    (standing : RankTwo.LocalApplication.SourceHypothesis S L)
    (f : FlagMarking S L V V₁ V₂) (localData : LocalConfiguration M f)
    (hTL : (S : Subgroup G) ≤ normalizer (L : Set G))
    (hK : K ∈ Yz L (S : Subgroup G) (markedZ f.module) (markedV f.module))
    (hn : Tv (S : Subgroup G) (markedV f.module) ≤ normalizer (K : Set G))
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV f.module)) =
      pCore 2 (Gv (markedV f.module)))
    (hgen : K = ⁅K, Stellmacher.elementaryAbelianMaxJ (Tv (S : Subgroup G) (markedV f.module))⁆)
    (d0 : let e := FullAction.sourceEarlierData f localData hTL hK hn hchar hgen
      DoubledCoordinates K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
        e.selected.1.1 e.normalizeL e.fixSeed)
    (hc : let e := FullAction.sourceEarlierData f localData hTL hK hn hchar hgen
      ⁅plusImage K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
          e.normalizeL e.fixSeed K,
        plusImage K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
          e.normalizeL e.fixSeed (Lv L (markedV f.module))⁆ = ⊥) :
    let e := FullAction.sourceEarlierData f localData hTL hK hn hchar hgen
    ∃ d : DoubledCoordinates K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
        e.selected.1.1 e.normalizeL e.fixSeed,
      plusImage K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
        e.normalizeL e.fixSeed
        (Stellmacher.elementaryAbelianMaxJ (Tv (S : Subgroup G) (markedV f.module))) =
          BinaryLinearThree.R.map (modelEmbedding d) ∧
      plusImage K L (S : Subgroup G) (markedZ f.module) (markedV f.module)
        e.normalizeL e.fixSeed (ChapterB.baumann (S : Subgroup G)) =
          BinaryLinearThree.R.map (modelEmbedding d) :=
  exists_radical_images_of_marked standing f localData
    (FullAction.sourceEarlierData f localData hTL hK hn hchar hgen) d0 hc
end Source


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
