module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalNormalizer
public import Theory.GroupTheory.Amalgam.ParabolicRecognition
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Maximal local normalizers in the primitive cubic amalgam

The candidates are the actual nonidentity subgroups of the common overlap
whose normalizer covers the first local group modulo the overlap and moves
the first vertex while fixing the second. All normalizers are intersections
inside the original, possibly infinite, completion. Finiteness is needed only
for the overlap and the local groups.

Choose a candidate with maximal first local normalizer. Its edge normalizer
has index two in the second local normalizer and is proper in the original
two-group overlap. If a nonidentity characteristic subgroup of that edge
normalizer were normal in the first local normalizer, the normalizer condition
in the overlap would strictly enlarge the first local normalizer. The second
local normalizer still supplies a mover, contradicting the chosen maximality.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), Section 5,
printed pp.394--395; the maximal-normalizer step of (5.3).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G]

/-- The literal local normalizer at one end of the base edge. -/
def localNormalizer (F : Bool → Subgroup G) (Q : Subgroup G) (i : Bool) : Subgroup G :=
  normalizer (Q : Set G) ⊓ F i

/-- The literal edge stabilizer inside the normalizer. -/
def edgeNormalizer (F : Bool → Subgroup G) (Q : Subgroup G) : Subgroup G :=
  normalizer (Q : Set G) ⊓ (F false ⊓ F true)

/-- Goldschmidt's set `S_{αβ}`, with local transitivity expressed by its
equivalent index-three condition on the original overlap cosets. -/
structure NormalizerCandidate (F : Bool → Subgroup G) (Q : Subgroup G) : Prop where
  nontrivial : Q ≠ ⊥
  le_overlap : Q ≤ F false ⊓ F true
  left_index : (F false ⊓ F true).relIndex (localNormalizer F Q false) = 3
  right_mover : ¬ localNormalizer F Q true ≤ F false

variable {F : Bool → Subgroup G}

theorem edgeNormalizer_eq_inf (Q : Subgroup G) :
    edgeNormalizer F Q = localNormalizer F Q false ⊓ localNormalizer F Q true := by
  ext x
  simp only [edgeNormalizer, localNormalizer, mem_inf]
  tauto

theorem edgeNormalizer_le_local (Q : Subgroup G) (i : Bool) :
    edgeNormalizer F Q ≤ localNormalizer F Q i := by
  cases i
  · exact fun _ hx => ⟨hx.1, hx.2.1⟩
  · exact fun _ hx => ⟨hx.1, hx.2.2⟩

theorem NormalizerCandidate.le_edge {Q : Subgroup G} (hQ : NormalizerCandidate F Q) :
    Q ≤ edgeNormalizer F Q :=
  le_inf Q.le_normalizer hQ.le_overlap

theorem CubicTreeAction.finite_localNormalizer (h : CubicTreeAction F)
    (Q : Subgroup G) (i : Bool) : Finite (localNormalizer F Q i) := by
  let : Finite (F i) := h.finite i
  exact Finite.of_injective (Subgroup.inclusion (show localNormalizer F Q i ≤ F i from
    inf_le_right)) (Subgroup.inclusion_injective _)

private theorem exists_three_in_local (h : CubicTreeAction F)
    (Q : Subgroup G) (i : Bool)
    (hi : (F false ⊓ F true).relIndex (localNormalizer F Q i) = 3) :
    ∃ X : Subgroup (F i), Nat.card X = 3 ∧
      X.map (F i).subtype ≤ normalizer (Q : Set G) := by
  let L := localNormalizer F Q i
  let : Finite L := h.finite_localNormalizer Q i
  have hd : 3 ∣ Nat.card L := by
    rw [← hi]
    exact ((F false ⊓ F true).subgroupOf L).index_dvd_card
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 hd
  let f : L →* F i := Subgroup.inclusion inf_le_right
  have hf : Function.Injective f := Subgroup.inclusion_injective _
  refine ⟨(zpowers x).map f, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf, Nat.card_zpowers, hx]
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact y.property.1

/-- A normalizer transitive at both ends would put its subgroup in the
trivial common normal core. -/
theorem CubicTreeAction.normalized_overlap_eq_bot_of_local_indices
    (h : CubicTreeAction F) (Q : Subgroup G) (hQT : Q ≤ F false ⊓ F true)
    (hleft : (F false ⊓ F true).relIndex (localNormalizer F Q false) = 3)
    (hright : (F false ⊓ F true).relIndex (localNormalizer F Q true) = 3) : Q = ⊥ := by
  obtain ⟨X, hX, hXN⟩ := exists_three_in_local h Q false hleft
  obtain ⟨Y, hY, hYN⟩ := exists_three_in_local h Q true hright
  exact h.normalized_overlap_eq_bot_of_three_subgroups Q hQT X Y hX hY hXN hYN

theorem CubicTreeAction.overlap_relIndex (h : CubicTreeAction F) (i : Bool) :
    (F false ⊓ F true).relIndex (F i) = 3 := by
  have hc := h.card_neighbor_base i
  rw [Subgroup.CosetGeometry.RankTwo.card_neighbor_base] at hc
  change (F (!i)).relIndex (F i) = 3 at hc
  cases i
  · simpa only [Bool.not_false, inf_relIndex_left] using hc
  · simpa only [Bool.not_true, inf_relIndex_right] using hc

theorem NormalizerCandidate.right_index_two (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q) :
    (F false ⊓ F true).relIndex (localNormalizer F Q true) = 2 := by
  let : Finite (localNormalizer F Q true) := h.finite_localNormalizer Q true
  have hi := h.overlap_relIndex true
  have hle := Subgroup.relIndex_le_of_le_right
    (show localNormalizer F Q true ≤ F true from inf_le_right) (by omega :
      (F false ⊓ F true).relIndex (F true) ≠ 0)
  have hn0 : (F false ⊓ F true).relIndex (localNormalizer F Q true) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hn1 : (F false ⊓ F true).relIndex (localNormalizer F Q true) ≠ 1 := by
    intro he
    exact hQ.right_mover ((Subgroup.relIndex_eq_one.mp he).trans inf_le_left)
  have hn3 : (F false ⊓ F true).relIndex (localNormalizer F Q true) ≠ 3 := by
    intro he
    exact hQ.nontrivial
      (h.normalized_overlap_eq_bot_of_local_indices Q hQ.le_overlap hQ.left_index he)
  omega

theorem NormalizerCandidate.edge_normal_in_right (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q) :
    ((edgeNormalizer F Q).subgroupOf (localNormalizer F Q true)).Normal := by
  apply Subgroup.normal_of_index_eq_two
  have he : (edgeNormalizer F Q).subgroupOf (localNormalizer F Q true) =
      (F false ⊓ F true).subgroupOf (localNormalizer F Q true) := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨x.property.1, hx⟩⟩
  rw [he]
  exact hQ.right_index_two h

theorem NormalizerCandidate.edge_lt_overlap (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q) :
    edgeNormalizer F Q < F false ⊓ F true := by
  refine lt_of_le_of_ne inf_le_right ?_
  intro he
  have hle : F false ⊓ F true ≤ localNormalizer F Q true :=
    he ▸ edgeNormalizer_le_local Q true
  have hm := Subgroup.relIndex_mul_relIndex (F false ⊓ F true)
    (localNormalizer F Q true) (F true) hle inf_le_right
  rw [hQ.right_index_two h, h.overlap_relIndex true] at hm
  omega

/-- Maximality is only among candidates with a containing first local normalizer. -/
structure MaximalNormalizerCandidate (F : Bool → Subgroup G) (Q : Subgroup G)
    : Prop extends NormalizerCandidate F Q where
  maximal : ∀ R : Subgroup G, NormalizerCandidate F R →
    localNormalizer F Q false ≤ localNormalizer F R false →
    localNormalizer F R false = localNormalizer F Q false

theorem CubicTreeAction.exists_maximalNormalizerCandidate (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q) :
    ∃ R : Subgroup G, MaximalNormalizerCandidate F R ∧
      localNormalizer F Q false ≤ localNormalizer F R false := by
  classical
  let T := F false ⊓ F true
  let : Finite (F false) := h.finite false
  let : Finite T := Finite.of_injective (Subgroup.inclusion inf_le_left)
    (Subgroup.inclusion_injective _)
  let C := {R : Subgroup G | NormalizerCandidate F R ∧
    localNormalizer F Q false ≤ localNormalizer F R false}
  have hf : C.Finite := by
    apply (Set.finite_range (fun P : Subgroup T => P.map T.subtype)).subset
    intro R hR
    exact ⟨R.subgroupOf T, Subgroup.map_subgroupOf_eq_of_le hR.1.le_overlap⟩
  obtain ⟨R, hR, hmax⟩ := Set.exists_max_image C
    (fun R => Nat.card (localNormalizer F R false)) hf ⟨Q, hQ, le_rfl⟩
  refine ⟨R, ⟨hR.1, ?_⟩, hR.2⟩
  intro K hK hRK
  let : Finite (localNormalizer F K false) := h.finite_localNormalizer K false
  exact (Subgroup.eq_of_le_of_card_ge hRK (hmax K ⟨hK, hR.2.trans hRK⟩)).symm

/-- The maximal local normalizer satisfies the original characteristic-normal
exclusion required by the local pushing-up theorem. -/
theorem MaximalNormalizerCandidate.characteristic_normal_eq_bot
    (h : CubicTreeAction F) {Q : Subgroup G} (hQ : MaximalNormalizerCandidate F Q)
    (K : Subgroup G) (hKE : K ≤ edgeNormalizer F Q)
    [(K.subgroupOf (edgeNormalizer F Q)).Characteristic]
    [(K.subgroupOf (localNormalizer F Q false)).Normal] : K = ⊥ := by
  classical
  by_contra hK
  let T := F false ⊓ F true
  let E := edgeNormalizer F Q
  let L := localNormalizer F Q false
  have hKL : K ≤ L := hKE.trans (edgeNormalizer_le_local Q false)
  have hLN : L ≤ normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mp inferInstance
  have hEN : normalizer (E : Set G) ≤ normalizer (K : Set G) := by
    have he : (K.subgroupOf E).map E.subtype = K :=
      Subgroup.map_subgroupOf_eq_of_le hKE
    rw [← he]
    exact Subgroup.normalizer_le_normalizer_characteristic_image E (K.subgroupOf E)
  have hRN : localNormalizer F Q true ≤ normalizer (K : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (edgeNormalizer_le_local Q true)).mp
      (hQ.toNormalizerCandidate.edge_normal_in_right h)).trans hEN
  have hLL : L ≤ localNormalizer F K false := le_inf hLN inf_le_right
  have hKK : NormalizerCandidate F K := by
    refine ⟨hK, hKE.trans inf_le_right, ?_, ?_⟩
    · let : Finite (localNormalizer F K false) := h.finite_localNormalizer K false
      have hlo := Subgroup.relIndex_le_of_le_right hLL
        (show T.relIndex (localNormalizer F K false) ≠ 0 from
          Subgroup.index_ne_zero_of_finite)
      have hhi := Subgroup.relIndex_le_of_le_right
        (show localNormalizer F K false ≤ F false from inf_le_right)
        (show T.relIndex (F false) ≠ 0 by rw [h.overlap_relIndex false]; decide)
      have hc := hQ.left_index
      have ht := h.overlap_relIndex false
      change T.relIndex L = 3 at hc
      change T.relIndex (F false) = 3 at ht
      change T.relIndex (localNormalizer F K false) = 3
      omega
    · intro hle
      exact hQ.right_mover ((le_inf hRN inf_le_right).trans hle)
  have heq := hQ.maximal K hKK hLL
  let : Finite (F false) := h.finite false
  let : Finite T := Finite.of_injective (Subgroup.inclusion inf_le_left)
    (Subgroup.inclusion_injective _)
  let : Group.IsNilpotent T := h.primitive.sylow.isPGroup.isNilpotent
  have hproper : E.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact not_le_of_gt (hQ.toNormalizerCandidate.edge_lt_overlap h)
  obtain ⟨x, hxN, hxE⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (E.subgroupOf T) hproper)
  have hxN' : (x : G) ∈ normalizer (E : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq (show E ≤ T from inf_le_right)] at hxN
    exact hxN
  have hxLK : (x : G) ∈ localNormalizer F K false := ⟨hEN hxN', x.property.1⟩
  have hxL : (x : G) ∈ L := by
    change (x : G) ∈ localNormalizer F Q false
    rwa [← heq]
  exact hxE ⟨hxL.1, x.property⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
