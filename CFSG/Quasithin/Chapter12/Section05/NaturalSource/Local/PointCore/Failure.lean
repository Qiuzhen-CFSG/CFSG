module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Quotient
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Radical
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The actual quotient configuration under failure of point-core containment

The star notation denotes images in G₁/O₂(G₁) under its literal projection.
A normal component K₁ has K₁/O₂(K₁) isomorphic to its star image, and this
isomorphism sends each representative to its original coset. This identifies
the three remaining model alternatives on that embedded image.

Under failure of V ≤ O₂(G₁), the image V* is elementary of order eight,
is fully moved by L₁*, and is irreducible under the image of N_L(V₁).
M₁* normalizes V*, and the component contains both V* and the original Y*.
The final theorem assembles this configuration from Hypothesis 12.2.3 and
LocalComponents. Constructing the remaining LocalComponents rows and the
three model exclusions stays with this local owner. The final exterior
assembly remains with qt-d-1251-source.

Source: Aschbacher--Smith, proof of 12.5.8(1), printed p.820.
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

/-- The literal image in the original point-centralizer core quotient. -/
@[expose] def pointCoreImage (A : Subgroup G) :
    Subgroup (s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) :=
  (A.subgroupOf (s.marking.Gi 1)).map (QuotientGroup.mk' (pCore 2 (s.marking.Gi 1)))

omit [Finite G] in
theorem pointCoreImage_mono {A B : Subgroup G} (hAB : A ≤ B) :
    s.pointCoreImage A ≤ s.pointCoreImage B := map_mono (comap_mono hAB)

omit [Finite G] in
theorem pointCoreImage_seed_elementary : IsElementaryAbelian 2 (s.pointCoreImage V) := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf (s.marking.Gi 1)) :=
    IsElementaryAbelian.subgroupOf (D.le_sylow.trans s.sylow_le_G₁)
  exact IsElementaryAbelian.map _

theorem pointCoreImage_seed_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hfail : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    Nat.card (s.pointCoreImage V) = 8 :=
  s.seed_core_image_card_of_failure h hfail _ (QuotientGroup.ker_mk' _)

omit [Finite G] in
theorem pointCoreImage_M₁_normalizes_seed :
    s.pointCoreImage (s.marking.Mi 1) ≤ normalizer (s.pointCoreImage V : Set _) := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  have hVH : V ≤ H := D.le_sylow.trans s.sylow_le_G₁
  have hn : (s.marking.Mi 1).subgroupOf H ≤ normalizer (V.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hVH]
    exact comap_mono (inf_le_left.trans s.normalizes)
  exact (map_mono hn).trans ((V.subgroupOf H).le_normalizer_map q)

/-- Relative normality identifies the intrinsic component quotient with its star image. -/
@[expose] def pointComponentCoreEquivImage {K : Subgroup G}
    (hKH : K ≤ s.marking.Gi 1) (hn : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    (K ⧸ pCore 2 K) ≃* s.pointCoreImage K := by
  let := hn
  let e := (subgroupOfEquivOfLe hKH).symm
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (coreQuotientEquivImage 2 (K.subgroupOf (s.marking.Gi 1)))

omit [Finite G] in
/-- The component identification retains the original quotient projection. -/
theorem pointComponentCoreEquivImage_mk {K : Subgroup G}
    (hKH : K ≤ s.marking.Gi 1) (hn : (K.subgroupOf (s.marking.Gi 1)).Normal) (k : K) :
    (s.pointComponentCoreEquivImage hKH hn (QuotientGroup.mk' (pCore 2 K) k) :
      s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) =
      QuotientGroup.mk' (pCore 2 (s.marking.Gi 1)) ⟨k, hKH k.property⟩ := by
  let := hn
  let e := (subgroupOfEquivOfLe hKH).symm
  change (coreQuotientEquivImage 2 (K.subgroupOf (s.marking.Gi 1))
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e) (QuotientGroup.mk' (pCore 2 K) k)) :
      s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) = _
  erw [QuotientGroup.congr_mk', coreQuotientEquivImage_apply_mk]
  rfl

/-- Irreducibility of the original upper chief factor in the literal core image. -/
theorem pointCoreImage_seed_invariant_interval
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {B : Subgroup (s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1))}
    (hB : B ≤ s.pointCoreImage V)
    (hn : s.pointCoreImage (L ⊓ s.marking.Gi 1) ≤ normalizer (B : Set _)) :
    B = ⊥ ∨ B = s.pointCoreImage V := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := V ⊓ (B.comap q).map H.subtype
  have hVH : V ≤ H := D.le_sylow.trans s.sylow_le_G₁
  have h7c : (s.marking.Vi 7).subgroupOf H ≤ pCore 2 H := by
    have hh := comap_mono (f := H.subtype) (s.seven_le_point_core h)
    change (s.marking.Vi 7).subgroupOf H ≤ ((pCore 2 H).map H.subtype).comap H.subtype at hh
    rwa [comap_map_eq_self_of_injective H.subtype_injective] at hh
  have h7A : s.marking.Vi 7 ≤ A := by
    refine le_inf (s.marking.subspace_le _) ?_
    intro v hv
    let vH : H := ⟨v, hVH (s.marking.subspace_le _ hv)⟩
    refine ⟨vH, ?_, rfl⟩
    change q vH ∈ B
    have he : q vH = 1 := (QuotientGroup.eq_one_iff _).mpr (h7c hv)
    rw [he]
    exact B.one_mem
  have hnA : L ⊓ H ≤ normalizer (A : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    refine ⟨(mem_normalizer_iff.mp (D.normalizes hg.1) x).mp hx.1, ?_⟩
    obtain ⟨v, hv, rfl⟩ := hx.2
    let gH : H := ⟨g, hg.2⟩
    refine ⟨gH * v * gH⁻¹, ?_, rfl⟩
    have hng : q gH ∈ normalizer (B : Set _) := hn (mem_map_of_mem q hg)
    have hb := (mem_normalizer_iff.mp hng (q v)).mp hv
    change q (gH * v * gH⁻¹) ∈ B
    simpa only [map_mul, map_inv] using hb
  rcases s.marking.point_upper_invariant_interval_of_component A h7A inf_le_left hnA
    with he | he
  · left
    apply bot_unique
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hB hx
    have hvA : (v : G) ∈ A := ⟨hv, ⟨v, hx, rfl⟩⟩
    have hv7 : (v : G) ∈ s.marking.Vi 7 := he ▸ hvA
    exact mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr (h7c hv7))
  · right
    apply le_antisymm hB
    rintro x ⟨v, hv, rfl⟩
    have hvA : (v : G) ∈ A := he.symm ▸ hv
    obtain ⟨w, hw, hwv⟩ := hvA.2
    have hewv : w = v := Subtype.ext hwv
    exact hewv ▸ hw

/-- The source model alternatives transferred to the actual star-quotient component. -/
theorem point_core_failure_image_models (c : LocalComponents s)
    (hfail : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    ClassicalGroup.IsPSL (s.pointCoreImage (c.K 1)) 5 2 ∨
      Nonempty (s.pointCoreImage (c.K 1) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (s.pointCoreImage (c.K 1) ≃* Janko4.Model) := by
  let e := s.pointComponentCoreEquivImage (c.component 1 (Or.inl rfl)).1
    (c.normal 1 (Or.inl rfl))
  rcases (s.point_core_failure_large c hfail).1 with hm | em | ej
  · exact Or.inl (hm.of_mulEquiv e.symm)
  · exact Or.inr (Or.inl ⟨e.symm.trans em.some⟩)
  · exact Or.inr (Or.inr ⟨e.symm.trans ej.some⟩)

/-- The literal quotient configuration left by failure of the point-core conclusion.
The three remaining model exclusions belong to this same local owner. -/
theorem point_core_failure_quotient_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (c : LocalComponents s)
    (hfail : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    Nat.card (s.pointCoreImage V) = 8 ∧
    IsElementaryAbelian 2 (s.pointCoreImage V) ∧
    s.pointCoreImage V ≤ s.pointCoreImage (c.K 1) ∧
    s.pointCoreImage s.Y ≤ s.pointCoreImage (c.K 1) ∧
    s.pointCoreImage (s.marking.Mi 1) ≤ normalizer (s.pointCoreImage V : Set _) ∧
    ⁅s.pointCoreImage V, s.pointCoreImage (s.marking.Li 1)⁆ = s.pointCoreImage V ∧
    (∀ B ≤ s.pointCoreImage V,
      s.pointCoreImage (L ⊓ s.marking.Gi 1) ≤ normalizer (B : Set _) →
      B = ⊥ ∨ B = s.pointCoreImage V) ∧
    Nonempty ((c.K 1 ⧸ pCore 2 (c.K 1)) ≃* s.pointCoreImage (c.K 1)) ∧
    (ClassicalGroup.IsPSL (s.pointCoreImage (c.K 1)) 5 2 ∨
      Nonempty (s.pointCoreImage (c.K 1) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (s.pointCoreImage (c.K 1) ≃* Janko4.Model)) := by
  have hy := (s.point_core_failure_large c hfail).2
  exact ⟨s.pointCoreImage_seed_card h hfail, s.pointCoreImage_seed_elementary,
    s.pointCoreImage_mono (s.seed_le_point_residual.trans (c.contains 1 (Or.inl rfl))),
    s.pointCoreImage_mono hy, s.pointCoreImage_M₁_normalizes_seed,
    s.seed_core_image_fully_moved _,
    (fun _ hB hn => s.pointCoreImage_seed_invariant_interval h hB hn),
    ⟨s.pointComponentCoreEquivImage (c.component 1 (Or.inl rfl)).1 (c.normal 1 (Or.inl rfl))⟩,
    s.point_core_failure_image_models c hfail⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
