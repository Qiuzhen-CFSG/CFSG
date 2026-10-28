module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Selected.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Normality.Centralizer

/-!
# The elementary eight and its fusion four inside the local centralizer

Put `E = Q ∩ Qᵍ` and `V = E ∩ F`, where `F` is the canonical fusion eight.
The nonidentity elements of V are exactly the ambient z-conjugates in E.
Consequently every ambient element normalizing E also normalizes V. Both
cores normalize E, so their join, and hence its t-centralizer, normalizes
both subgroups. The chosen t lies in E outside V, giving E = V × ⟨t⟩.
The previously proved ambient equality C_G(E) = E supplies self-centrality
in the literal local centralizer, with all subgroup inclusions retained.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.4–2.5 and 4.1(1), pp.34 and 38–39.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {z : G}

@[expose] public def plane (z g : G) : Subgroup G :=
  coreIntersection z g ⊓ fusionCore z

@[expose] public def ambient (z t g : G) : localCentralizer z t g →* G :=
  (Centralizer t).subtype.comp (localCentralizer z t g).subtype

omit [Finite G] in
public theorem ambient_injective (z t g : G) : Function.Injective (ambient z t g) :=
  (Centralizer t).subtype_injective.comp (localCentralizer z t g).subtype_injective

@[expose] public def eight (z t g : G) : Subgroup (localCentralizer z t g) :=
  (coreIntersection z g).comap (ambient z t g)

@[expose] public def four (z t g : G) : Subgroup (localCentralizer z t g) :=
  (plane z g).comap (ambient z t g)

public theorem plane_fusion_iff (_h : Hypotheses z) (d : FusionEightData z)
    (g : G) {x : G} (hx : x ∈ coreIntersection z g) :
    x ∈ plane z g ↔ x = 1 ∨ IsConj z x := by
  change (x ∈ coreIntersection z g ∧ x ∈ fusionCore z) ↔ _
  rw [d.mem_iff]
  have hxQ : x ∈ coreInG z := hx.1
  tauto

public theorem join_normalizes_eight (h : Hypotheses z) (a : SelectedFusionData h) :
    coreInG z ⊔ conjugateCore z a.g ≤ normalizer (coreIntersection z a.g : Set G) :=
  sup_le (NonnormalRecognition.core_normalizes_intersection h a.g a.fused_mem a.fused_ne)
    (NonnormalRecognition.conjugate_core_normalizes_intersection h a.g a.fused_mem a.fused_ne)

public theorem normalizer_eight_le_normalizer_plane (h : Hypotheses z)
    (d : FusionEightData z) (g : G) :
    normalizer (coreIntersection z g : Set G) ≤ normalizer (plane z g : Set G) := by
  intro m hm
  apply mem_normalizer_iff.mpr
  intro x
  have hE := mem_normalizer_iff.mp hm x
  constructor
  · intro hx
    have hxE := hE.mp hx.1
    apply (plane_fusion_iff h d g hxE).mpr
    rcases (plane_fusion_iff h d g hx.1).mp hx with rfl | hc
    · exact Or.inl (by simp)
    · exact Or.inr (hc.trans (isConj_iff.mpr ⟨m, rfl⟩))
  · intro hx
    have hxE := hE.mpr hx.1
    apply (plane_fusion_iff h d g hxE).mpr
    rcases (plane_fusion_iff h d g hx.1).mp hx with he | hc
    · exact Or.inl ((MulAut.conj m).map_eq_one_iff.mp he)
    · exact Or.inr (hc.trans (isConj_iff.mpr ⟨m, rfl⟩).symm)

public theorem eight_le_centralizer (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) :
    coreIntersection z a.g ≤ Centralizer t := by
  let : IsElementaryAbelian 2 (coreIntersection z a.g) := a.intersection_elementary
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : coreIntersection z a.g) ⟨t, htE⟩)

private theorem eight_subgroupOf_le (h : Hypotheses z) (a : SelectedFusionData h) (t : G) :
    (coreIntersection z a.g).subgroupOf (Centralizer t) ≤ localCentralizer z t a.g := by
  intro x hx
  exact mem_sup_left hx.1

public def eightEquiv (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) :
    eight z t a.g ≃* coreIntersection z a.g :=
  (subgroupOfEquivOfLe (eight_subgroupOf_le h a t)).trans
    (subgroupOfEquivOfLe (eight_le_centralizer h a htE))

public theorem eight_card (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) : Nat.card (eight z t a.g) = 8 :=
  (Nat.card_congr (eightEquiv h a htE).toEquiv).trans a.intersection_card

public theorem eight_elementary (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) : IsElementaryAbelian 2 (eight z t a.g) := by
  let : IsElementaryAbelian 2 (coreIntersection z a.g) := a.intersection_elementary
  let : IsElementaryAbelian 2 ((coreIntersection z a.g).subgroupOf (Centralizer t)) :=
    IsElementaryAbelian.subgroupOf (eight_le_centralizer h a htE)
  exact IsElementaryAbelian.subgroupOf (eight_subgroupOf_le h a t)

public theorem eight_normal (h : Hypotheses z) (a : SelectedFusionData h) (t : G) :
    (eight z t a.g).Normal := by
  constructor
  intro x hx m
  exact (mem_normalizer_iff.mp (join_normalizes_eight h a m.property) _).mp hx

public theorem four_normal (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) (t : G) : (four z t a.g).Normal := by
  constructor
  intro x hx m
  exact (mem_normalizer_iff.mp (normalizer_eight_le_normalizer_plane h d a.g
    (join_normalizes_eight h a m.property)) _).mp hx

omit [Finite G] in
public theorem four_le_eight (z t g : G) : four z t g ≤ eight z t g :=
  comap_mono inf_le_left

public def fourEquiv (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) : four z t a.g ≃* plane z a.g :=
  (subgroupOfEquivOfLe (show (plane z a.g).subgroupOf (Centralizer t) ≤
    localCentralizer z t a.g from fun _ hx => mem_sup_left hx.1.1)).trans
    (subgroupOfEquivOfLe (inf_le_left.trans (eight_le_centralizer h a htE)))

public theorem four_card (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g) :
    Nat.card (four z t a.g) = 4 :=
  (Nat.card_congr (fourEquiv h a htE).toEquiv).trans
    (Selected.intersection_fusion_card h d a.g a.fused_mem a.fused_ne a.intersection_ne_fusion)

public theorem eight_self_centralizing (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) :
    centralizer (eight z t a.g : Set (localCentralizer z t a.g)) = eight z t a.g := by
  let : IsElementaryAbelian 2 (eight z t a.g) := eight_elementary h a htE
  apply le_antisymm ?_ (eight z t a.g).le_centralizer
  intro x hx
  change ambient z t a.g x ∈ coreIntersection z a.g
  change ambient z t a.g x ∈ NonnormalRecognition.coreIntersection z a.g
  rw [← NonnormalRecognition.coreIntersection_self_centralizing h a.g a.fused_mem a.fused_ne]
  intro y hy
  let yE : coreIntersection z a.g := ⟨y, hy⟩
  have hc := hx ((eightEquiv h a htE).symm yE) ((eightEquiv h a htE).symm yE).property
  exact congrArg (ambient z t a.g) hc

@[expose] public def centralElement (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) : localCentralizer z t a.g :=
  ⟨distinguished t, mem_sup_left htE.1⟩

public theorem centralElement_mem_center (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) : centralElement h a htE ∈
      center (localCentralizer z t a.g) := by
  apply mem_center_iff.mpr
  intro x
  apply ambient_injective z t a.g
  exact mem_centralizer_singleton_iff.mp (x : Centralizer t).property

public theorem centralElement_order (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) (ht : orderOf t = 2) :
    orderOf (centralElement h a htE) = 2 := by
  rw [← orderOf_injective (ambient z t a.g) (ambient_injective z t a.g)]
  exact ht

public theorem centralElement_not_four (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t) : centralElement h a htE ∉ four z t a.g := by
  intro hx
  apply hnt
  exact d.fusion t hx.2 (fun he => by simp [he] at ht)

private theorem line_cases {K : Type*} [Group K] [Finite K] {w x : K} (hw : orderOf w = 2)
    (hx : x ∈ zpowers w) : x = 1 ∨ x = w := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hw] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hnlt : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

public theorem four_disjoint_central (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    Disjoint (four z t a.g) (zpowers (centralElement h a htE)) := by
  apply disjoint_iff_inf_le.mpr
  rintro x ⟨hx, hxT⟩
  rcases line_cases (centralElement_order h a htE ht) hxT with rfl | rfl
  · exact one_mem _
  · exact (centralElement_not_four h d a htE ht hnt hx).elim

public theorem eight_eq_four_sup_central (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    eight z t a.g = four z t a.g ⊔ zpowers (centralElement h a htE) := by
  let : (four z t a.g).Normal := four_normal h d a t
  have hle : four z t a.g ⊔ zpowers (centralElement h a htE) ≤ eight z t a.g :=
    sup_le (four_le_eight z t a.g) (zpowers_le.mpr htE)
  apply (eq_of_le_of_card_ge hle ?_).symm
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (four z t a.g) (zpowers (centralElement h a htE)) (by
      rw [(four z t a.g).normalizer_eq_top]; exact le_top)
  rw [(four_disjoint_central h d a htE ht hnt).eq_bot, card_bot,
    four_card h d a htE, Nat.card_zpowers, centralElement_order h a htE ht,
    one_mul] at hc
  rw [eight_card h a htE, ← hc]

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam
