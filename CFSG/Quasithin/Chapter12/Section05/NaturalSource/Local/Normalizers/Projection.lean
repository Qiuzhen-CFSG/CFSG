module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Source
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.ComponentIntersection
public import Theory.GroupTheory.CentralProductProjection.Normalizer
public import Theory.GroupTheory.PResidual.NormalizerImage

/-!
# The literal point-component projection in the normalizer argument

The original point-core lies in the original Sylow and normalizes L₁.
Since L₁ is perfect, normalization of its image in G₁/O₂(G₁) lifts back
to L₁. Together with the already proved local generation and factorization,
this reduces Gᵢ ≤ N_G(L), for i = 3,6, to the projected local intersection
inside K₁*. The projection retains the whole commuting centralizer factor.

In each of the three large point models the outer action is a two-group,
so the original Sylow supplies the cover required for this equivalence.
The projected subgroup contains the literal Sylow intersection with K₁*,
normalizes the original local-residual intersection, and keeps the normal
closure of Y* = O²(P)* inside the original point parabolic. These are the
inputs to the model-overgroup exclusions in the remainder of 12.5.4.

The radical row and those model exclusions remain with qt-d-1251-local;
this reduction does not use the generation-one exclusion. The earlier
structural theorem remains with qt-d-1222-source, and qt-d-1251-source
owns final exterior assembly.
Source: Aschbacher--Smith, 12.5.4, printed p.819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

omit [Finite G] in
/-- The full original point-core normalizes the perfect point residual. -/
theorem pointCore_normalizes_point_residual :
    (s.marking.Gi 1).pCoreIn 2 ≤ normalizer (s.marking.Li 1 : Set G) := by
  have hc : (s.marking.Gi 1).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le s.sylow_le_G₁] using
      pCoreIn_le_sylow (s.marking.Gi 1) (T.subtype s.sylow_le_G₁)
  exact hc.trans (s.sylow_normalizes_Li 1 (.inl rfl))

/-- Normalizer control lifts through the original point-core quotient. -/
theorem pointCoreImage_normalizes_point_iff (A : Subgroup G) (hA : A ≤ s.marking.Gi 1) :
    s.pointCoreImage A ≤ normalizer (s.pointCoreImage (s.marking.Li 1) : Set _) ↔
      A ≤ normalizer (s.marking.Li 1 : Set G) := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (s.marking.Li 1).subgroupOf H
  let : Group.IsPerfect (s.marking.Li 1) := s.marking.Li_perfect 1
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (s.marking.Li_le_Gi 1)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (s.marking.Li_le_Gi 1)).symm.surjective
  have hp : IsPPerfect 2 B := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (B ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (B ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (B ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (B ⧸ N) inferInstance
  have hn : q.ker ≤ normalizer (B : Set H) := by
    rw [QuotientGroup.ker_mk']
    intro x hx y
    exact s.pointCore_normalizes_point_residual (mem_map_of_mem H.subtype hx) (y : G)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  change (A.subgroupOf H).map q ≤ normalizer (B.map q : Set _) ↔ _
  rw [map_le_iff_le_comap,comap_normalizer_map_of_pPerfect q B hp hk hn]
  rw [←subgroupOf_normalizer_eq (s.marking.Li_le_Gi 1)]
  constructor
  · intro he a ha
    exact he (show (⟨a,hA ha⟩ : H) ∈ A.subgroupOf H from ha)
  · exact fun he => comap_mono he

/-- The full preimage in K₁* of the projection along its centralizer. -/
@[expose] def localPointProjection (K : Subgroup G) (i : ℕ) :
    Subgroup (s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) :=
  s.pointCoreImage K ⊓ (s.pointCoreImage (s.marking.Gi i ⊓ s.marking.Gi 1) ⊔
    centralizer (s.pointCoreImage K : Set _))

/-- The original local intersection controls both required ambient normalizers. -/
theorem local_intersection_normalizes_point_iff
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.marking.Gi i ≤ s.marking.M ↔
      s.marking.Gi i ⊓ s.marking.Gi 1 ≤ normalizer (s.marking.Li 1 : Set G) := by
  constructor
  · intro hm
    have hn : s.marking.Gi i ⊓ s.marking.Gi 1 ≤
        normalizer (L ⊓ s.marking.Gi 1 : Set G) :=
      (le_inf (inf_le_left.trans hm) (inf_le_right.trans (s.marking.Gi 1).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    exact hn.trans (normalizer_le_normalizer_characteristic_image
      (L ⊓ s.marking.Gi 1) (solvableResidual (L ⊓ s.marking.Gi 1 : Subgroup G)))
  · intro hn
    apply (s.local_normalizer_le_M_iff_point_control_from_source h i hi).mpr
    have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
    exact (le_inf (Subgroup.centralizer_le_normalizer _)
      ((centralizer_le (s.marking.V₁_le_Vi i hidx)).trans (Subgroup.centralizer_le_normalizer _))).trans hn

/-- Projection reduces the ambient normalizer problem when the outer action is a two-group. -/
theorem local_normalizer_iff_point_projection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ≤ s.marking.Gi 1) (hLK : s.marking.Li 1 ≤ K)
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)))
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.marking.Gi i ≤ s.marking.M ↔
      s.localPointProjection K i ≤ normalizer (s.pointCoreImage (s.marking.Li 1) : Set _) := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := s.pointCoreImage K
  let A := s.pointCoreImage (s.marking.Gi i ⊓ H)
  let B := s.pointCoreImage (s.marking.Li 1)
  let R := (T.subtype s.sylow_le_G₁).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let := hN
  let : C.Normal := Subgroup.Normal.map hN q (QuotientGroup.mk'_surjective _)
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  have hRA : (R : Subgroup _) ≤ A :=
    s.pointCoreImage_mono (le_inf (s.sylow_le_Gi i hidx) s.sylow_le_G₁)
  have hRB : (R : Subgroup (H ⧸ pCore 2 H)) ≤ normalizer (B : Set (H ⧸ pCore 2 H)) :=
    (s.pointCoreImage_normalizes_point_iff (T : Subgroup G) s.sylow_le_G₁).mpr
      (s.sylow_normalizes_Li 1 (.inl rfl))
  rw [s.local_intersection_normalizes_point_iff h i hi,
    ←s.pointCoreImage_normalizes_point_iff (s.marking.Gi i ⊓ H) inf_le_right]
  exact sylow_component_projection_normalizes_iff C A B R (s.pointCoreImage_mono hLK) hRA hRB
    (ho.of_equiv (MulAut.outerCongr (s.pointComponentCoreEquivImage hK hN)))

/-- Relative normality of the original local residual survives the exact point quotient. -/
theorem pointCoreImage_local_intersection_normalized
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.pointCoreImage (s.marking.Gi i ⊓ s.marking.Gi 1) ≤
      normalizer (s.pointCoreImage (s.marking.Li i ⊓ s.marking.Gi 1) : Set _) := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  have hNi : s.marking.Gi i ≤ normalizer (s.marking.Li i : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (s.marking.Li_le_Gi i)).mp
    rcases hi with rfl | rfl
    · exact (s.local_three_component_from_source h).2
    · exact (s.local_six_component_source h).2
  have hn : (s.marking.Gi i ⊓ H).subgroupOf H ≤
      normalizer ((s.marking.Li i ⊓ H).subgroupOf H : Set H) := by
    intro a ha x
    have hh := (mem_normalizer_iff.mp (hNi ha.1) (x : G))
    change ((x : G) ∈ s.marking.Li i ∧ (x : G) ∈ H) ↔ _
    constructor
    · intro hx
      exact ⟨hh.mp hx.1,H.mul_mem (H.mul_mem a.property hx.2) (H.inv_mem a.property)⟩
    · intro hx
      exact ⟨hh.mpr hx.1,x.property⟩
  exact (map_mono hn).trans (((s.marking.Li i ⊓ H).subgroupOf H).le_normalizer_map q)


/-- The actual projected actor preserves the intersection of the original local
residual image with the point component. -/
theorem point_projection_normalizes_residual_intersection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.localPointProjection K i ≤
      normalizer (s.pointCoreImage (s.marking.Li i ⊓ s.marking.Gi 1) ⊓
        s.pointCoreImage K : Set _) := by
  let q := QuotientGroup.mk' (pCore 2 (s.marking.Gi 1))
  let := hN
  let : (s.pointCoreImage K).Normal := Subgroup.Normal.map hN q (QuotientGroup.mk'_surjective _)
  exact component_projection_normalizes_intersection _ _ _
    (s.pointCoreImage_local_intersection_normalized h i hi)

/-- The projected closure of the original Y stays inside the original local
residual intersection; it is not an arbitrarily chosen model subgroup. -/
theorem projected_Y_span_le_original_intersection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) (hY : s.Y ≤ K)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    conjugateSpanBy (s.pointCoreImage s.Y) (s.localPointProjection K i) ≤
      s.pointCoreImage (s.marking.Li i ⊓ s.marking.Gi 1) ⊓ s.pointCoreImage K := by
  apply conjugateSpanBy_le
  · exact le_inf (s.pointCoreImage_mono (le_inf (s.Y_le_local_residual i hi)
      ((map_subtype_le (pResidual 2 s.P)).trans (s.P_le_M₁.trans inf_le_right))))
      (s.pointCoreImage_mono hY)
  · exact s.point_projection_normalizes_residual_intersection h hN i hi


/-- The projection retains the original Sylow intersection in the point component. -/
theorem point_projection_contains_original_sylow {K : Subgroup G}
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    ∃ S : Sylow 2 (s.pointCoreImage K),
      (S : Subgroup _) = (s.pointCoreImage (T : Subgroup G)).subgroupOf (s.pointCoreImage K) ∧
      (S : Subgroup _) ≤ (s.localPointProjection K i).subgroupOf (s.pointCoreImage K) := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := (T.subtype s.sylow_le_G₁).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let C := s.pointCoreImage K
  let := hN
  let : C.Normal := Subgroup.Normal.map hN q (QuotientGroup.mk'_surjective _)
  obtain ⟨S,hS⟩ := R.exists_subgroupOf_eq_of_normal C
  refine ⟨S,hS,?_⟩
  rw [hS]
  intro x hx
  refine ⟨x.property,?_⟩
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  exact mem_sup_left (s.pointCoreImage_mono
    (le_inf (s.sylow_le_Gi i hidx) s.sylow_le_G₁) hx)

/-- The projected normal closure of Y* stays in the actual point parabolic. -/
theorem projected_Y_span_le_point_parabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) (hY : s.Y ≤ K)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    conjugateSpanBy (s.pointCoreImage s.Y) (s.localPointProjection K i) ≤
      s.pointCoreImage (s.marking.Mi 1) ⊓ s.pointCoreImage K := by
  apply (s.projected_Y_span_le_original_intersection h hN hY i hi).trans
  apply inf_le_inf_right
  apply s.pointCoreImage_mono
  exact le_inf ((inf_le_left.trans (s.marking.Li_le_L i)).trans le_sup_left) inf_le_right

private theorem large_point_outer_two
    {A : Type*} [Group A] [Finite A]
    (hm : ClassicalGroup.IsPSL A 5 2 ∨ Nonempty (A ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (A ≃* Janko4.Model)) : IsPGroup 2 (MulAut.Outer A) := by
  rcases hm with hm | hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = Fintype.card (ZMod 2) := by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF
    let a := (e.trans (Atlas.fieldEquivPSL 5 (FiniteField.ringEquivOfCardEq hc))).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5))
    exact (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup (.inr rfl)).of_equiv
      (MulAut.outerCongr a).symm
  · exact Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two.of_equiv
      (MulAut.outerCongr hm.some).symm
  · exact Janko4.AdequateLocal.outer_isPGroup_two.of_equiv (MulAut.outerCongr hm.some).symm

/-- The three large source models discharge the outer-action premise of the projection reduction. -/
theorem local_normalizer_iff_large_point_projection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model))
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.marking.Gi i ≤ s.marking.M ↔
      s.localPointProjection K i ≤ normalizer (s.pointCoreImage (s.marking.Li 1) : Set _) :=
  s.local_normalizer_iff_point_projection h hK.1 hLK hN (large_point_outer_two hm) i hi

/-- All three large source models supply the projected closure containment with Y ≤ K proved. -/
theorem large_point_projected_Y_span_le_parabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model))
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    conjugateSpanBy (s.pointCoreImage s.Y) (s.localPointProjection K i) ≤
      s.pointCoreImage (s.marking.Mi 1) ⊓ s.pointCoreImage K :=
  s.projected_Y_span_le_point_parabolic h hN
    (s.Y_le_point_component_of_large_model h hK hN hm) i hi

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
