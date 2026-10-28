module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoHull.LocalCover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoHull.ClassicalCover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoHull.ExceptionalCover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.FourGroup
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.AmbientQuotient

/-!
# Invariant rank-two hulls from intrinsic normalizer coverage

Write K, T, N for the actual images of L, S, M in I/C_I(L). The faithfully
embedded plane R = V₂⁺ is normal in N. Its relation [R,Y₊⁺] = R and normality
of K place R inside K; in particular R is a genuine four-group there.
The component Sylow subgroup P is exactly T ∩ K and normalizes R.

An intrinsic model cover makes N_K(P) joined with N_K(R) proper. Therefore
the smaller join Q = N_K(P) joined with N ∩ K is proper. T normalizes both
terms, so Q is T-invariant even when the actor has outer automorphisms.
This discharges the ambient action and quotient transports without assuming
parabolic recognition, node fixation, or characteristic-two parabolic cores.

The classical and exceptional coverage theorems discharge this input for all
five rank-two families. The degree-one derived and Tits alternatives contradict
`n > 1`. Thus `rankTwo_invariantHull` supplies the geometric hull without any
additional coverage premise. Characteristic-two maximality and the parabolic
core calculation belong to the separate recognition assembly.
Source: Aschbacher--Smith, 15.3.43(e) and its characteristic-two paragraph,
printed p.1140; 1.1.5(3)(a)--(c), pp.501--502; A.2.3--4, p.33.
-/

public section

open Subgroup CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {H : Type*} [Group H]

private theorem actor_normalizes_borel (K T : Subgroup H) [K.Normal] :
    T ≤ normalizer (borel K T : Set H) := by
  have hK : T ≤ normalizer (K : Set H) := by
    rw [normalizer_eq_top]
    exact le_top
  exact (le_inf hK
    (((le_inf T.le_normalizer hK).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf

/-- The join of the Borel with the local component intersection is proper
by intrinsic coverage. Both factors are invariant under the outer actor, so
the join is the required invariant hull. No node-fixation claim is needed. -/
theorem invariantHull_of_fourGroupNormalizerCover (K T N R : Subgroup H)
    [K.Normal] (hTN : T ≤ N) (P : Sylow 2 K)
    (hP : (P : Subgroup K).map K.subtype = T ⊓ K)
    (hRK : R ≤ K) (hNR : N ≤ normalizer (R : Set H))
    (hRe : IsElementaryAbelian 2 R) (hRc : Nat.card R = 4)
    (hcover : FourGroupNormalizerCover K) : InvariantHull K T N := by
  let : IsElementaryAbelian 2 R := hRe
  have he : IsElementaryAbelian 2 (R.subgroupOf K) := IsElementaryAbelian.subgroupOf hRK
  have hc : Nat.card (R.subgroupOf K) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRK).toEquiv).trans hRc
  have hnP : (P : Subgroup K) ≤ normalizer (R.subgroupOf K : Set K) := by
    rw [← subgroupOf_normalizer_eq hRK]
    intro x hx
    apply hNR
    apply hTN
    have hx' : (x : H) ∈ T ⊓ K := by
      rw [← hP]
      exact mem_map_of_mem K.subtype hx
    exact hx'.1
  have hi := hcover P (R.subgroupOf K) he hc hnP
  have hNK : N.subgroupOf K ≤ normalizer (R.subgroupOf K : Set K) := by
    rw [← subgroupOf_normalizer_eq hRK]
    exact fun _ hx => hNR hx
  have hsmall : (borel K T).subgroupOf K ⊔ N.subgroupOf K < ⊤ := by
    rw [borel_subgroupOf_eq_sylowNormalizer K T P hP]
    exact lt_of_le_of_lt (sup_le_sup_left hNK _) hi
  have hproper : borel K T ⊔ (N ⊓ K) < K := by
    have hm := (map_lt_map_iff_of_injective K.subtype_injective).mpr hsmall
    rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le (borel_le K T), subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, range_subtype] at hm
  refine ⟨borel K T ⊔ (N ⊓ K), le_sup_left, hproper, ?_, le_sup_right⟩
  apply (le_inf (actor_normalizes_borel K T) ?_).trans
    ((borel K T).normalizer_inf_normalizer_le_normalizer_sup (N ⊓ K))
  apply (le_inf (hTN.trans N.le_normalizer) ?_).trans inf_normalizer_le_normalizer_inf
  rw [normalizer_eq_top]
  exact le_top

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

omit [Finite G] in
/-- The literal plane survives in the action quotient, lies in the component,
and is normalized by the local image. Thus the intrinsic cover is applied to
a genuine nontrivial two-subgroup of the component, not to an outer subgroup. -/
theorem quotient_fourGroup_for_cover :
    c.toComponentAction.image V₂ ≤ c.toComponentAction.image L ∧
    c.toComponentAction.image M ≤ normalizer
      (c.toComponentAction.image V₂ : Set c.toComponentAction.Quotient) ∧
    IsElementaryAbelian 2 (c.toComponentAction.image V₂) ∧
    Nat.card (c.toComponentAction.image V₂) = 4 := by
  obtain ⟨⟨e⟩, hVM, hn, hcomm⟩ := c.four_group_image
  have hYL : c.toComponentAction.image Yplus ≤ c.toComponentAction.image L :=
    map_mono (fun _ hx => c.y_le_component hx)
  have hVL : c.toComponentAction.image V₂ ≤ c.toComponentAction.image L := by
    rw [← hcomm]
    exact (commutator_mono le_rfl hYL).trans (commutator_le_right _ _)
  refine ⟨hVL, (normal_subgroupOf_iff_le_normalizer hVM).mp hn, ?_,
    (Nat.card_congr e.toEquiv).symm.trans c.plane_two_card⟩
  let : IsElementaryAbelian 2 V₂ := c.plane_two_elementary
  let : IsElementaryAbelian 2 (V₂.subgroupOf I) :=
    IsElementaryAbelian.subgroupOf (c.plane_two_le.trans (sylow_le_local c |>.trans inf_le_right))
  exact IsElementaryAbelian.map c.toComponentAction.quotientMap

/-- The outer action and the nontrivial inner two-subgroup are discharged;
only the intrinsic matrix/building calculation remains explicit. -/
theorem rankTwo_invariantHull_of_localCover
    (hcover : FourGroupNormalizerCover (c.toComponentAction.image L)) :
    InvariantHull (c.toComponentAction.image L) (c.toComponentAction.image S)
      (c.toComponentAction.image M) := by
  obtain ⟨P, hP⟩ := quotient_component_sylow c
  obtain ⟨hVK, hn, he, hc⟩ := quotient_fourGroup_for_cover c
  exact invariantHull_of_fourGroupNormalizerCover _ _ _ _
    (map_mono (fun _ hx => c.sylow_le_M hx)) P hP hVK hn he hc hcover

/-- Every rank-two alternative over a field of degree greater than one admits
a proper hull containing the Borel and local component intersection and
normalized by the full Sylow actor in the actual action quotient. The model
cover supplies properness; the quotient four-group and invariance are derived
from the reduced configuration. -/
theorem rankTwo_invariantHull {n : ℕ} (hn : 1 < n)
    (hm : ChapterA.Section02.IsTheoremCRankTwoModel (c.toComponentAction.image L) n) :
    InvariantHull (c.toComponentAction.image L) (c.toComponentAction.image S)
      (c.toComponentAction.image M) := by
  apply rankTwo_invariantHull_of_localCover c
  cases hm with
  | linear _ hi => exact linear_fourGroupNormalizerCover hn hi
  | symplectic _ hi => exact symplectic_fourGroupNormalizerCover hn hi
  | g2 _ hi => exact g2_fourGroupNormalizerCover hn hi
  | triality _ hi => exact triality_fourGroupNormalizerCover hn hi
  | ree_f4 _ hm _ hi => exact ree_fourGroupNormalizerCover hm hi
  | symplectic_derived he _ => omega
  | g2_derived he _ => omega
  | tits he _ => omega

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
