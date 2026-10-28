module

public import Stellmacher.Recognition.Parrott.LocalGeneratorData
public import Stellmacher.Recognition.Parrott.SylowGenerators
public import Stellmacher.Recognition.Parrott.CentralizerGenerators
public import Stellmacher.Recognition.Parrott.NormalizerCompatibleGenerators
public import Theory.SpecificGroups.Tits.RecognitionLocalRelations

/-!
# Parrott's local generators and presentation words

For compatible normalized centralizer and normalizer frames, the local word
algebra proves the 36 relators other than VI(i). The presentation words generate
exactly H ∨ N: the forward inclusion uses their membership in the local groups;
the reverse inclusion recovers every local generator from the presentation words.
The named-word identities and involution classes are retained for the separate
proof of VI(i). No eighth-power braid relation is asserted here.

The normalized Sylow construction, centralizer extension, and compatible
normalizer construction supply these frames from the original recognition
hypotheses. The last normalization may replace x by xz, so the word algebra
and all subsequent conclusions use the same final compatible pair. The actual
F,T,t,v remain unchanged throughout.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, pp.678–682, and §6, p.684.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

namespace ParrottNormalizerGeneratorData

variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)
include k

/-- The exact generator correspondence from p.684, retaining the original z,t,v. -/
@[expose] public def words : Tits.ParrottGenerator → G :=
  Tits.parrottRecognitionWords z n.t n.v f.u f.w f.a f.b f.c f.d f.x f.y f.r k.s

/-- All 36 local presentation relators. The separate braid relation is excluded. -/
public theorem relators_except_braid (i : Tits.ParrottRelatorIndex)
    (hi : i ≠ .vi_r1_r8) : FreeGroup.lift k.words (Tits.parrottRelator i) = 1 :=
  k.localRelations.relators_except_braid i hi

/-- The square equation used to recover the prescribed involution. -/
public theorem x_sq : f.x ^ 2 = f.y * z := k.localRelations.eq04

/-- The chosen y is an involution in the exponent-two sense used in the words. -/
public theorem y_sq : f.y ^ 2 = 1 := k.localRelations.y_sq

/-- The third named word recovers the supplied central generator t. -/
public theorem r3 : FreeGroup.lift k.words Tits.parrottR3 = n.t := k.localRelations.r3

/-- The fifth named word recovers the original involution z. -/
public theorem r5 : FreeGroup.lift k.words Tits.parrottR5 = z := k.localRelations.r5

/-- The seventh named word, with the printed factor order. -/
public theorem r7 : FreeGroup.lift k.words Tits.parrottR7 = f.x * f.b * f.c * f.w * n.t :=
  k.localRelations.r7

/-- The product form of equation (20), since r is an involution. -/
public theorem rtr : f.r * n.t * f.r = f.w * f.u * n.v * z := k.localRelations.rtr

/-- The other expression for s₇r₇ used in the braid argument. -/
public theorem s7_mul_r7 :
    k.words .s7 * FreeGroup.lift k.words Tits.parrottR7 = f.w * f.u * n.v * z :=
  k.localRelations.s7_mul_r7

/-- The presentation anchor is the original z. -/
public theorem anchor : k.words .s1 * (k.words .s5) ^ 2 = z := k.localRelations.anchor

/-- Both required involution classes, with exact orders rather than just squares. -/
public theorem involution_classes :
    orderOf f.r = 2 ∧ IsConj f.r z ∧ orderOf k.s = 2 ∧ IsConj k.s n.v :=
  ⟨f.r_order, f.r_conjugate, k.s_order, k.s_conjugate⟩

/-- The normalizer generator is in the actual second normalizer. -/
public theorem s_mem_normalizer : k.s ∈ normalizer (e.F : Set G) := by
  rw [← k.normalizer_generators]
  exact mem_sup_right (mem_zpowers k.s)

/-- Containing the presentation words is equivalent to containing both actual
local groups. This retains the subgroup information needed in global generation. -/
public theorem words_mem_iff (L : Subgroup G) :
    (∀ i, k.words i ∈ L) ↔
      centralizer ({z} : Set G) ≤ L ∧ normalizer (e.F : Set G) ≤ L := by
  constructor
  · intro hwords
    obtain ⟨_, _, _, _, _, ha, hb, hc, hd, hx, _, hr, hs⟩ :=
      (k.localRelations.mem_iff L).mp hwords
    have hT : (e.sylow : Subgroup G) ≤ L := by
      rw [← f.sylow_generators]
      apply (closure_le _).mpr
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> assumption
    constructor
    · rw [← f.centralizer_generators]
      exact sup_le hT (zpowers_le.mpr hr)
    · rw [← k.normalizer_generators]
      exact sup_le hT (zpowers_le.mpr hs)
  · rintro ⟨hH, hN⟩
    have hTH : (e.sylow : Subgroup G) ≤ centralizer ({z} : Set G) := by
      rw [← f.centralizer_generators]
      exact le_sup_left
    have hT := hTH.trans hH
    obtain ⟨hz, ht, hv, hu, hw, ha, hb, hc, hd, hx, hy⟩ := f.toParrottSylowGeneratorData.local_mem_sylow
    apply (k.localRelations.mem_iff L).mpr
    exact ⟨hT hz, hT ht, hT hv, hT hu, hT hw, hT ha, hT hb, hT hc,
      hT hd, hT hx, hT hy, hH f.r_mem_centralizer, hN k.s_mem_normalizer⟩

/-- The ten presentation words generate precisely H ∨ N. No ambient generation
or braid relation is assumed to prove this equality. -/
public theorem closure_words :
    closure (Set.range k.words) =
      centralizer ({z} : Set G) ⊔ normalizer (e.F : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro g ⟨i, rfl⟩
    exact (k.words_mem_iff _).mpr ⟨le_sup_left, le_sup_right⟩ i
  · apply sup_le
    · exact ((k.words_mem_iff _).mp
        (fun i => subset_closure (Set.mem_range_self i))).1
    · exact ((k.words_mem_iff _).mp
        (fun i => subset_closure (Set.mem_range_self i))).2

end ParrottNormalizerGeneratorData

/-- Extend the supplied normalizer-fusion configuration to compatible local
generators satisfying all source equations (1)–(26). The elementary bases and
generation of the actual J,T,H,N are fields of this same pair of frames. -/
public theorem ParrottNormalizerFusionData.exists_local_generators
    [Finite G] [IsSimpleGroup G] (n : ParrottNormalizerFusionData e)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (Σ f : ParrottCentralizerGeneratorData n, ParrottNormalizerGeneratorData f) := by
  obtain ⟨f⟩ := n.exists_sylow_generators hns hN h
  obtain ⟨f'⟩ := f.exists_centralizer_generators hns hN h
  exact f'.nonempty_compatible_generator_data hns hN h

/-- Compatible local generators exist under the original recognition hypotheses,
with no generator equations or auxiliary existence assumptions. The dependent
packet retains the actual second elementary subgroup and normalizer witnesses
for the separate braid and ambient-order arguments. -/
public theorem parrott_local_generators_exists [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ e : ParrottSecondElementaryData z, ∃ n : ParrottNormalizerFusionData e,
      Nonempty (Σ f : ParrottCentralizerGeneratorData n, ParrottNormalizerGeneratorData f) := by
  obtain ⟨e, ⟨n⟩⟩ := parrott_normalizer_fusion_exists hns hN h
  exact ⟨e, n, n.exists_local_generators hns hN h⟩

/-- The actual local presentation, its original anchor, and its generation
equality hold simultaneously for one compatible pair constructed from the
original hypotheses. Only the separately owned relation VI(i) is excluded. -/
public theorem parrott_local_presentation_exists [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ e : ParrottSecondElementaryData z, ∃ n : ParrottNormalizerFusionData e,
      ∃ f : ParrottCentralizerGeneratorData n, ∃ k : ParrottNormalizerGeneratorData f,
        (∀ i : Tits.ParrottRelatorIndex, i ≠ .vi_r1_r8 →
          FreeGroup.lift k.words (Tits.parrottRelator i) = 1) ∧
        k.words .s1 * (k.words .s5) ^ 2 = z ∧
        closure (Set.range k.words) =
          centralizer ({z} : Set G) ⊔ normalizer (e.F : Set G) := by
  obtain ⟨e, n, ⟨⟨f, k⟩⟩⟩ := parrott_local_generators_exists hns hN h
  exact ⟨e, n, f, k, k.relators_except_braid, k.anchor, k.closure_words⟩

end Stellmacher.Recognition
