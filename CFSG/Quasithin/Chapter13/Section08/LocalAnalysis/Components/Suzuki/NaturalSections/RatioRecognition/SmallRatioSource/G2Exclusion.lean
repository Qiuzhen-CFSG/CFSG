module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.G2
public import Theory.Representation.G2NaturalInvolutionExclusion

/-!
# Excluding ordinary G₂ modules in the marked Chapter 13 classification

The source hypotheses recognize the actual normal component's action as the
natural six-space over the field of order 2^n. Its full binary normalizer
has involution displacement at least 2n, including the field-automorphism
coset. The original marked involution has displacement at most two, excluding
every n > 1. No assumption that this involution belongs to the component is
needed. The separate derived binary G₂ case remains in the source catalogue.

Source: Aschbacher–Smith B.4.6, K.3 and 13.5.21, pp.88–90,457,923–924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The natural G₂ component cannot occur with the source's small involution. -/
theorem g2_excluded_of_small_involution (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : L ⧸ center L ≃* Atlas.G2.Model F.Carrier)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) ((ρ t - 1).range) ≤ 2) : False := by
  obtain ⟨M⟩ := SourceClassification.g2_natural_action h F hF e
  rcases F with @⟨K, hField, hFinite, hChar, hAlg, n, hn, hcard⟩
  have hAlgEq : hAlg = ZMod.algebra K 2 := Subsingleton.elim _ _
  subst hAlg
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let := h.layer_normal
  have hd := Atlas.G2.Natural.Normalizer.ambient_involution_displacement_ge K
    ρ L M.groupEquiv M.linearEquiv (fun g v => M.intertwines g v)
    h.faithful (show 2 ≤ n by change 1 < n at hF; omega) hcard t ht
  change 1 < n at hF
  omega

/-- The literal Theorem C model row is excluded, with its original field witness. -/
theorem g2_model_excluded_of_small_involution (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At (L ⧸ center L) (2 ^ n))
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) ((ρ t - 1).range) ≤ 2) : False := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ n by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let B : BinaryField := { Carrier := F, degree := n, degree_pos := by omega, card_eq := hcard }
  exact g2_excluded_of_small_involution h B (by change 1 < n; omega) e t ht hr

end CFSG.Quasithin.ChapterB.SmallRatioClassification
