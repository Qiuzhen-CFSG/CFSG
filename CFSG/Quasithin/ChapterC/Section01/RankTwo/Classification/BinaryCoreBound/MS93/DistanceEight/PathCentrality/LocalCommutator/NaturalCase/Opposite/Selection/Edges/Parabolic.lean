module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Parabolic.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Parabolic.Model

/-!
# The actual opposite parabolic in MS93 (4.4.1)(1)

Select a moving element of Z_a and a compatible flag fixing its class in
W/B_c. Opposite coordinates give zero fixed subgroup on the actual U_c.
Two-perfect idempotence first proves normalization of the original cyclic
displacement by O²(P). Its order is at most four, and its global residual
commutators lie in U_c, so the binary parabolic lifting theorem gives
normalization by all of P.

The resulting ParabolicSeed retains the original projection, actual B_c,
and ambient displacement. No favorable pairing, trapped radius,
displacement-plane identity or edge identity is assumed. The parent Edges
assembly still owns the subsequent small-displacement and edge calculations.

Source: Meierfrankenfeld–Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1)(1), printed pp.890–891, the conjugate of F₂ on p.891.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R} {f : FrameAt a c}

/-- The full selected parabolic normalizes the original ambient displacement. -/
theorem FixedSeed.displacement_normalized (s : FixedSeed geometry f)
    (common : CommonFacts R source geometry) (hb : 2 < geometry.b R)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) :
    (parabolic f.sectionData.projection s.flag s.side).map (stabilizer R c).subtype ≤
      normalizer (⁅zpowers s.element, Q R c⁆ : Subgroup (FreeAmalgam R)) := by
  let S := stabilizer R c
  let K := ⁅zpowers s.element, Q R c⁆
  let K₀ := K.subgroupOf S
  let U₀ := (U R c).subgroupOf S
  let P := parabolic f.sectionData.projection s.flag s.side
  let := finite_stabilizer R c
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer (U_normalized c)
  have hQG : Q R c ≤ S := fun _ hx => hx.1
  have hKdis : K ≤ ⁅Z R a,Q R c⁆ := commutator_mono (zpowers_le.mpr s.element_mem) le_rfl
  have hdisQ : ⁅Z R a,Q R c⁆ ≤ Q R c :=
    ((commutator_mono (Z_le_localZSpan R a c) le_rfl).trans
      (span_commutator_le_span a c)).trans (localZSpan_le_Q R hc hd.le hb)
  have hKS : K ≤ S := hKdis.trans (hdisQ.trans hQG)
  have hker : f.sectionData.projection.ker = (Q R c).subgroupOf S :=
    f.sectionData.module_section.projection_kernel
  have hn : P ≤ normalizer (K₀ : Set S) := by
    apply Parabolic.small_normalized_of_residual f.sectionData.projection
      f.sectionData.module_section.projection_surjective _ U₀ f.naturalU
      s.flag s.side K₀ _ _ _ _
      (s.displacement_normalized_twoResidual source hb hc hd)
    · rw [hker]
      exact (Q_isPGroup R source.two_group source.core_le c hc).comap_subtype
    · rw [hker]
      exact comap_mono (hKdis.trans hdisQ)
    · let : Finite (⁅Z R a,Q R c⁆ : Subgroup (FreeAmalgam R)) :=
        Finite.of_injective (inclusion (hdisQ.trans hQG)) (inclusion_injective _)
      rw [Nat.card_congr (subgroupOfEquivOfLe hKS).toEquiv]
      exact (Nat.card_le_card_of_injective (inclusion hKdis) (inclusion_injective _)).trans
        (displacement_card_le_four common ha hd)
    · exact (commutator_mono (comap_mono (s.displacement_le_B hb hc hd)) le_rfl).trans
        (FixedSeed.B_residual_commutator_le_U common hb hc)
    · rw [hker]
      exact (comap_mono (normalizer_commutator_ge_right (zpowers s.element) (Q R c))).trans
        (le_normalizer_comap S.subtype)
  have h := (map_mono (f := S.subtype) hn).trans (le_normalizer_map S.subtype)
  rwa [map_subgroupOf_eq_of_le hKS] at h

/-- The opposite natural action supplies the source conjugate of F₂,
including normalization in the amalgam, not just in a quotient. -/
theorem parabolicSeed_nonempty (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hn : ¬ ⁅Z R a,Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) : Nonempty (ParabolicSeed geometry f) := by
  obtain ⟨s⟩ := fixedSeed_nonempty source hc hd (by omega) hn f hop
  exact ⟨{
    toMovingSeed := s.toMovingSeed
    flag := s.flag
    weakBN := s.weakBN
    side := s.side
    natural_fixed_eq_bot := s.natural_fixed_eq_bot
    class_fixed := s.class_fixed
    displacement_normalized := s.displacement_normalized common (by omega) ha hc hd }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
