module
public import ABG.ChapterII.Section1.WreathedVNormalizerRestriction
public import ABG.ChapterII.Section1.WreathedFrameTransport
public import ABG.ChapterII.Section1.WreathedCentralProductNormalizer
public import ABG.ChapterII.Section2.AutomizerRestriction
public import Theory.GroupTheory.NormalizerFusionIndexControl

/-!
# Outer automizer of the wreathed quaternion central product

For an actual wreathed fusion frame, the outer automizer of its specified
central product V has index two or six. This is the N(V) calculation in
Alperin--Brauer--Gorenstein, Chapter II Section 1 Proposition 2, article
p. 12, `page-013.tex` of the source transcription. The denominator remains
V joined with its full ambient centralizer, as in the paper.

The normalizer restriction module shows that the canonical outer index
divides six by its action on the characteristic quaternion factor while
fixing the cyclic Sylow center. Here the centricity C_S(V) <= V and the
internal normalizer index two make two divide the ambient outer index:
restrict the normal denominator V C(V) to the Sylow normalizer. Conjugacy
invariance transports both divisibilities from the canonical central
product to the specified frame, leaving precisely two and six.
-/

namespace ABG.Wreathed

private theorem two_dvd_outer_map {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (W : Subgroup S)
    (hC : Subgroup.centralizer (W : Set S) ≤ W)
    (hN : W.relIndex (Subgroup.normalizer (W : Set S)) = 2) :
    2 ∣ outerAutomizerIndex (W.map (S : Subgroup G).subtype) := by
  let V := W.map (S : Subgroup G).subtype
  have hVS : V ≤ S := Subgroup.map_subtype_le W
  have hVW : V.subgroupOf (S : Subgroup G) = W :=
    Subgroup.comap_map_eq_self_of_injective (S : Subgroup G).subtype_injective W
  have hCP : (Subgroup.centralizer (V : Set G)).subgroupOf (S : Subgroup G) ≤
      V.subgroupOf (S : Subgroup G) := by
    rw [hVW]
    intro x hx
    apply hC
    intro w hw
    exact Subtype.ext (hx w (Subgroup.mem_map_of_mem _ hw))
  have hi : ((V ⊔ Subgroup.centralizer (V : Set G)).subgroupOf (S : Subgroup G)).relIndex
      ((Subgroup.normalizer (V : Set G)).subgroupOf (S : Subgroup G)) = 2 := by
    rw [Subgroup.sup_centralizer_subgroupOf_eq_of_centralizer_le _ _ hVS hCP,
      Subgroup.subgroupOf_normalizer_eq hVS, hVW]
    exact hN
  let N := Subgroup.normalizer (V : Set G)
  let D := V ⊔ Subgroup.centralizer (V : Set G)
  have heq : (D.subgroupOf (S : Subgroup G)).relIndex (N.subgroupOf (S : Subgroup G)) =
      (D.subgroupOf N).relIndex ((S : Subgroup G).subgroupOf N) := by
    simp only [Subgroup.subgroupOf, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq, Subgroup.range_subtype]
    rw [inf_comm N]
  let : (D.subgroupOf N).Normal := by
    dsimp only [D, N]
    rw [Subgroup.subgroupOf_sup V.le_normalizer (Subgroup.centralizer_le_normalizer _)]
    infer_instance
  have hdiv := Subgroup.relIndex_dvd_index_of_normal (D.subgroupOf N) ((S : Subgroup G).subgroupOf N)
  rw [← heq, hi] at hdiv
  exact hdiv

/-- The specified wreathed central product has outer automizer index two or six. -/
public theorem v_outer_automizer_index {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hframe : WreathedFusionFrame S n U V) :
    outerAutomizerIndex V = 2 ∨ outerAutomizerIndex V = 6 := by
  obtain ⟨P⟩ := nonempty_presentation hframe.1
  obtain ⟨s, hs⟩ := (hframe.presentation_representatives P).2
  have hindex : outerAutomizerIndex V =
      outerAutomizerIndex (P.V.map (S : Subgroup G).subtype) := by
    rw [← hs]
    exact outerAutomizerIndex_map _ (MulAut.conj (s : G))
  have hdvd : outerAutomizerIndex V ∣ 6 := by
    rw [hindex]
    exact canonical_v_outer_index_dvd_six S P
  have htwo : 2 ∣ outerAutomizerIndex V := by
    rw [hindex]
    apply two_dvd_outer_map S P.V ?_ P.V_normalizer_index
    rw [P.V_centralizer]
    exact le_sup_right
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hdvd
  clear hindex hs s P hframe
  interval_cases h : outerAutomizerIndex V <;> simp_all

end ABG.Wreathed
