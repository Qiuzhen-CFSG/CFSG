module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.ReciprocalAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Generation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.ShearTransport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.SourceShears
public import Mathlib.FieldTheory.Finite.GaloisField
/-!
# The reciprocal contradiction on the original source groups

The doubled marking extends to the full normalizer, where small fixed
codimension forces the reciprocal actor into the natural SL₃ component.
The two centralizer indices select the full plane radical. Transport by the
literal chosen conjugation gives its shear coordinates on B = V_M^g.
The selected star Sylow and G.1.6 quotient then contradict the nonsplit
central extension through their equal nonzero commutator planes.

Elementarity is supplied on the original omega closure by the source bridge,
without replacing the group or the star projection. The remaining doubled
Geometry is still this task's proof obligation. RankOneReduction retains its
explicit earlier-source owner qt-d-1222-shadow-rankone-recognition.
This conditional theorem does not assert the parameter exclusion.

Source: Aschbacher--Smith, 11.3.6, printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The doubled marking from 11.2.1 constructs the reciprocal plane action
from its original centralizer indices. -/
theorem shears_of_coordinates (d : Coordinates D S) [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (fullModule L V : Set G))
    (hr : 2*S.field.degree ≤ ChapterE.subgroupCorank A
      (A ⊓ centralizer (fullModule L V : Set G)))
    (hc : ChapterE.subgroupCorank (fullModule L V)
      (fullModule L V ⊓ centralizer (A : Set G)) ≤ 2*S.field.degree) :
    Nonempty (ShearCoordinates A (fullModule L V) S.field.Carrier) := by
  obtain ⟨m,⟨c⟩⟩ := d
  let q := m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let c' : BinaryConjugationSection L (fullModule L V) ⊥
      ((SL3DoubledNaturalOffenders.representation S.field.Carrier).comp q) :=
    { section_le := c.section_le
      kernel_le := c.kernel_le
      normalized := c.normalized
      coordinates := c.coordinates
      onto := c.onto
      kernel_eq := c.kernel_eq
      equivariant := by
        intro l w
        have he := c.equivariant l w
        ext i j
        exact congrFun (congrFun he i) j }
  apply ReciprocalAction.shears_of_section q
    (m.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
    c' ?_ hA S.field.degree_pos S.field.card_eq hr hc
  exact (fullModule_normalizer ⟨m,⟨c⟩⟩).le
/-- Apply the reciprocal calculation to the literal chosen conjugate, with
both centralizer indices transported by its inverse ambient map. -/
theorem shears_of_coordinates_map (d : Coordinates D S) [IsElementaryAbelian 2 A]
    (e : G ≃* G)
    (hA : A ≤ normalizer ((fullModule L V).map e.toMonoidHom : Set G))
    (hr : 2*S.field.degree ≤ ChapterE.subgroupCorank A
      (A ⊓ centralizer ((fullModule L V).map e.toMonoidHom : Set G)))
    (hc : ChapterE.subgroupCorank ((fullModule L V).map e.toMonoidHom)
      ((fullModule L V).map e.toMonoidHom ⊓ centralizer (A : Set G)) ≤ 2*S.field.degree) :
    Nonempty (ShearCoordinates A ((fullModule L V).map e.toMonoidHom) S.field.Carrier) := by
  let A₀ := A.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.map _
  have hnorm : A₀ ≤ normalizer (fullModule L V : Set G) := by
    have hh := (map_mono (f := e.symm.toMonoidHom) hA).trans
      (((fullModule L V).map e.toMonoidHom).le_normalizer_map e.symm.toMonoidHom)
    simpa [A₀,map_map] using hh
  have hrc := corank_centralizer_map (A := A) (B := (fullModule L V).map e.toMonoidHom) e.symm
  have hcc := corank_centralizer_map (A := (fullModule L V).map e.toMonoidHom) (B := A) e.symm
  have hcancel : ((fullModule L V).map e.toMonoidHom).map e.symm.toMonoidHom =
      fullModule L V := by simp [map_map]
  rw [hcancel] at hrc hcc
  have hr₀ : 2*S.field.degree ≤ ChapterE.subgroupCorank A₀
      (A₀ ⊓ centralizer (fullModule L V : Set G)) := by
    rw [hrc]
    exact hr
  have hc₀ : ChapterE.subgroupCorank (fullModule L V)
      (fullModule L V ⊓ centralizer (A₀ : Set G)) ≤ 2*S.field.degree := by
    rw [hcc]
    exact hc
  obtain ⟨c⟩ := shears_of_coordinates d hnorm hr₀ hc₀
  have he : A₀.map e.toMonoidHom = A := by simp [A₀,map_map]
  exact ⟨he ▸ c.map e⟩
open CommonCore Representation.SL2SylowFixedRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

private theorem contradiction_over_field {K : Type*} [Field K] [Finite K] [CharP K 2]
    (s : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S) (z : Geometry d H) (r : RankOneReduction S H)
    (hu : ChapterE.generationParameter H ≤ 2 * S.field.degree)
    (hK : Nat.card K = 2^(2*S.field.degree)) : False := by
  let : IsElementaryAbelian 2 (omegaClosure T H) :=
    CommonCore.source_omegaClosure_elementary s
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨e,R,g,hg,ha,hR,hP,hm⟩ := source_recognition_inputs s p hc d z r hu hK
  obtain ⟨c⟩ := quotientCoordinates_of_fixedSpaceHypotheses
    (NaturalRecognition.binaryAction T H e)
    (R.mapSurjective (f := e.toMonoidHom) e.surjective) hP
    (2*S.field.degree) (by have := S.nonbinary; omega) hK
  have hmodel := (residual_component s d r z.weak_escape z.s_value hu).2
  have hn := reciprocal_normalization s g d z hK hg ha hmodel
  have hdim : Module.finrank (ZMod 2) K = 2*S.field.degree :=
    NaturalTensor.finrank_field K hK
  have hr := quotient_multiplicity_sylow_bound (NaturalRecognition.binaryAction T H e) c
    (R.mapSurjective (f := e.toMonoidHom) e.surjective)
  rw [hm c,one_mul,hdim,
    source_fixedCodim_eq_corank e R _ (hg.trans s.outside.1.1.2) hR] at hr
  have hco := selected_rank s g d hK hg ha z.s_value hmodel
  rw [star_rank_eq_corank _ (hg.trans s.outside.1.1.2)] at hco
  obtain ⟨ds⟩ := shears_of_coordinates_map d (MulAut.conj g) hn hr hco.le
  have hBK : ((((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map
      (starProjection T H)) ≤ residualStar T H := by
    rw [← hR]
    exact map_subtype_le _
  exact source_shear_quotient_contradiction ds e (hg.trans s.outside.1.1.2) hBK R hR
    S.field.degree S.nonbinary S.field.card_eq hK hP c (hm c)

/-- The rank budget and the literal star quotient construct the reciprocal
shears and their nonsplit contradiction. Only the earlier rank-one reduction,
the doubled local geometry and preceding generation bound remain explicit. -/
theorem source_contradiction_of_geometry
    (s : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S) (z : Geometry d H) (r : RankOneReduction S H)
    (hu : ChapterE.generationParameter H ≤ 2 * S.field.degree) : False := by
  let K := GaloisField 2 (2*S.field.degree)
  have hn : 2*S.field.degree ≠ 0 := by have := S.field.degree_pos; omega
  have hK : Nat.card K = 2^(2*S.field.degree) := GaloisField.card 2 (2*S.field.degree) hn
  exact contradiction_over_field s p hc d z r hu hK

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
