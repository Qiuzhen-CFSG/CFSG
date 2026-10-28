module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalCubic
public import Theory.GroupTheory.InnerSupplementFullRank
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Cubic
public import Theory.SpecificGroups.SymplecticFour.Sylow.NoncyclicOddActor
public import Theory.SpecificGroups.G2.NoncyclicOddActor
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.CyclicOuter
/-!
# The point residual inside the normal rank-two component

In the original symplectic and G₂ rows, the cyclic outer group and
L₁=[L₁,T intersect L] force inner action. Both models have three-rank
at least two. The full-rank inner-supplement theorem therefore places
L₁-star in K-star, since its centralizing coordinate would increase the
ambient three-rank.

The original E₉ survives O₂(H). The existing root calculations applied
to this same subgroup identify O₂(L₁-star) with (T intersect K)-star.
The full kernel O₂(H) lies in O₂(L₁T), so lifting gives the literal
T intersect K <= O₂(L₁T). No intrinsic core is replaced by an intersection
with O₂(L), and no model or quotient-action conclusion is assumed.

Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
The Borel identifications are continued in AbelianNormalRankTwoBorel.
The outer-action exclusions, signed degree-three rows, module alternatives
and universal natural reduction remain with the source assembly.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hH hKH hgen in
/-- Full ambient three-rank removes the original residual’s centralizing coordinate. -/
theorem SourceHypothesis.original_full_rank_point_star_le_component
    (hn : (K.subgroupOf H).Normal)
    [IsMulCommutative (MulAut.Outer (actorImage H K))]
    (hcenter : center (actorImage H K) = ⊥) (hr : 2 ≤ primeRank 3 (actorImage H K)) :
    actorImage H (D.fullSetup hZ T z).L₁ ≤ actorImage H K := by
  let E := D.fullSetup hZ T z
  let A := actorImage H E.L₁
  let B := actorImage H K
  let q := QuotientGroup.mk' (pCore 2 H)
  let : B.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hTA : actorImage H T ≤ normalizer (A : Set (H ⧸ pCore 2 H)) := by
    have ht : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
      (le_inf hTH hTV).trans (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
    rintro _ ⟨x,hx,rfl⟩
    apply (E.L₁.subgroupOf H).le_normalizer_map q
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq hLH]
    exact ht hx
  have hstar : B ⊔ A ⊔ actorImage H T = ⊤ := by
    have hg := hgen
    rw [conjugateSpan_eq_of_normal H K T hKH hTH hn] at hg
    unfold B A actorImage
    rw [←Subgroup.map_sup,←Subgroup.map_sup,←subgroupOf_sup hKH hLH,
      ←subgroupOf_sup (sup_le hKH hLH) hTH,hg,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  obtain ⟨_,_,_,d,_⟩ := S.original_point_star_core_quotient D hZ z hz hTz hH
  let : IsElementaryAbelian 3 (A ⧸ pCore 2 A) :=
    IsElementaryAbelian.of_injective d.toMonoidHom d.injective
  exact inner_supplement_le_of_full_prime_rank A B (actorImage H T)
    (pCore_quotient_pCore_eq_bot 2) hcenter hr
    (S.original_star_three_rank D hZ z hz hH)
    (S.original_point_residual_inner_of_outer_abelian D hZ z hz hTz hH hn) hTA hstar

private theorem center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : center Y = ⊥) : center X = ⊥ := by
  apply bot_unique
  intro x hx
  exact mem_bot.mpr (e.map_eq_one_iff.mp
    (mem_bot.mp (h ▸ ((centerCongr e) ⟨x,hx⟩).property)))

include hz hTV hTz hH hKH hK hgen in
/-- The original residual image is contained in the normal symplectic component. -/
theorem SourceHypothesis.original_abelian_normal_symplectic_point_le
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) :
    actorImage H (D.fullSetup hZ T z).L₁ ≤ actorImage H K := by
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) (by omega))
  let e := (componentStarEquiv H K hKH hK).symm.trans
    (eK.trans (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hq))
  let : IsCyclic (MulAut.Outer (Theory.SpecificGroups.SymplecticFour.Sp F)) :=
    Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card
      hcard (by omega)
      Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
  let : IsCyclic (MulAut.Outer (actorImage H K)) := (MulAut.outerCongr e).isCyclic.mpr inferInstance
  exact S.original_full_rank_point_star_le_component D hZ z hz hTV hTz hH hKH hgen hn
    (center_eq_bot_of_equiv e Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot)
    ((primeRank_equiv 3 e).symm ▸ Theory.SpecificGroups.SymplecticFour.OddFieldActors.cubic_rank)

include hz hTV hTz hH hKH hK hgen in
/-- The original residual image is contained in the normal G₂ component. -/
theorem SourceHypothesis.original_abelian_normal_g2_point_le
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) :
    actorImage H (D.fullSetup hZ T z).L₁ ≤ actorImage H K := by
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) (by omega))
  let e := (componentStarEquiv H K hKH hK).symm.trans
    (eK.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hcard))
  let : IsCyclic (MulAut.Outer (Atlas.G2.Model F)) :=
    Atlas.G2.LieAutomorphismExtensions.outer_isCyclic hq
  let : IsCyclic (MulAut.Outer (actorImage H K)) := (MulAut.outerCongr e).isCyclic.mpr inferInstance
  exact S.original_full_rank_point_star_le_component D hZ z hz hTV hTz hH hKH hgen hn
    (center_eq_bot_of_equiv e (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq))
    ((primeRank_equiv 3 e).symm ▸ Atlas.G2.EvenThreeRank.two_le_primeRank)

include hz hTV hTz hH in
private theorem source_star_core_of_model
    (hn : (K.subgroupOf H).Normal)
    {X : Type*} [Group X] [Finite X] (e : actorImage H K ≃* X)
    (hle : actorImage H (D.fullSetup hZ T z).L₁ ≤ actorImage H K)
    (hcalc : ∀ (A P : Subgroup X), Group.IsSolvable A → P ≤ A →
      IsPGroup 3 P → (¬ IsCyclic P) → ∀ Q : Sylow 2 X,
      (Q : Subgroup X) ≤ normalizer (A : Set X) → A.pCoreIn 2 = (Q : Subgroup X)) :
    (actorImage H (D.fullSetup hZ T z).L₁).pCoreIn 2 =
      actorImage H ((T : Subgroup G) ⊓ K) := by
  let E := D.fullSetup hZ T z
  let A := actorImage H E.L₁
  let B := actorImage H K
  let C := A.subgroupOf B
  let q := QuotientGroup.mk' (pCore 2 H)
  let Y := C.map e.toMonoidHom
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  let Q := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let : B.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := Q.exists_subgroupOf_eq_of_normal B
  have hPT : (P : Subgroup B).map B.subtype = actorImage H ((T : Subgroup G) ⊓ K) := by
    rw [hP,subgroupOf_map_subtype]
    change actorImage H T ⊓ actorImage H K = _
    rw [inf_comm]
    change (K.comap H.subtype).map q ⊓ ((T : Subgroup G).comap H.subtype).map q =
      (((T : Subgroup G) ⊓ K).comap H.subtype).map q
    rw [comap_inf,inf_comm ((T : Subgroup G).comap H.subtype)]
    exact (map_inf_of_ker_le _ _ _ (show q.ker ≤ (T : Subgroup G).subgroupOf H by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTH))).symm
  have hTL : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    (le_inf hTH hTV).trans (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  have hnA : actorImage H T ≤ normalizer (A : Set (H ⧸ pCore 2 H)) :=
    by
      rintro _ ⟨x,hx,rfl⟩
      apply (E.L₁.subgroupOf H).le_normalizer_map q
      apply mem_map_of_mem
      rw [←subgroupOf_normalizer_eq (show E.L₁ ≤ H from fun x hx => hH.1.2 (Or.inl hx))]
      exact hTL hx
  have hnC : (P : Subgroup B) ≤ normalizer (C : Set B) := by
    intro x hx
    have hxT : (x : H ⧸ pCore 2 H) ∈ actorImage H T :=
      (map_mono (comap_mono inf_le_left)) (hPT ▸ mem_map_of_mem B.subtype hx)
    exact mem_normalizer_iff.mpr (fun y => mem_normalizer_iff.mp (hnA hxT) y.val)
  obtain ⟨_,_,_,d,_⟩ := S.original_point_star_core_quotient D hZ z hz hTz hH
  let : IsElementaryAbelian 3 (A ⧸ pCore 2 A) := IsElementaryAbelian.of_injective d.toMonoidHom d.injective
  let : Group.IsNilpotent (pCore 2 A) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable A := Group.isSolvable_of_ker_le_range
    (pCore 2 A).subtype (QuotientGroup.mk' (pCore 2 A))
    (by rw [range_subtype,QuotientGroup.ker_mk'])
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hle).toMonoidHom) (subgroupOfEquivOfLe hle).injective
  have hY : Group.IsSolvable Y := Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective C)
  let R : Sylow 3 E.L₁ := Classical.choice inferInstance
  let R₀ := (R : Subgroup E.L₁).map E.L₁.subtype
  let Rstar := actorImage H R₀
  have hRA : Rstar ≤ A := map_mono (comap_mono (map_subtype_le _))
  have hRB : Rstar ≤ B := hRA.trans hle
  obtain ⟨hR,hRc,_⟩ := S.original_point_sylow_star D hZ z hz hTz hH R
  let : IsElementaryAbelian 3 Rstar := hR
  let : IsElementaryAbelian 3 (Rstar.subgroupOf B) := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hRB).toMonoidHom (subgroupOfEquivOfLe hRB).injective
  let RX := (Rstar.subgroupOf B).map e.toMonoidHom
  let : IsElementaryAbelian 3 RX := IsElementaryAbelian.map e.toMonoidHom
  have hc : Nat.card RX = 3^2 := by
    rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe hRB).toEquiv]
    exact hRc
  have heq := hcalc Y RX hY (map_mono (comap_mono hRA))
    (IsElementaryAbelian.isPGroup 3 RX)
    (IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hc)
    (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    ((map_mono hnC).trans (C.le_normalizer_map e.toMonoidHom))
  have hcP : C.pCoreIn 2 = (P : Subgroup B) := by
    apply (map_injective (f := e.toMonoidHom) e.injective)
    rw [map_pCoreIn_of_injective 2 C e.toMonoidHom e.injective]
    exact heq
  have hh := congrArg (map B.subtype) hcP
  rw [map_pCoreIn_of_injective 2 C B.subtype B.subtype_injective,
    map_subgroupOf_eq_of_le hle] at hh
  exact hh.trans hPT

include hz hTV hTz hH hKH hK hgen in
/-- The symplectic root calculation identifies the intrinsic core of L₁-star. -/
theorem SourceHypothesis.original_abelian_normal_symplectic_star_core
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) :
    (actorImage H (D.fullSetup hZ T z).L₁).pCoreIn 2 =
      actorImage H ((T : Subgroup G) ⊓ K) := by
  have hle := S.original_abelian_normal_symplectic_point_le D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) (by omega))
  let e := (componentStarEquiv H K hKH hK).symm.trans
    (eK.trans (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hq))
  apply source_star_core_of_model S D hZ z hz hTV hTz hH hn e hle
  intro A P hA hPA hP hnc Q hnQ
  let _ := hA
  exact Theory.SpecificGroups.SymplecticFour.NoncyclicOddActor.twoCore_eq_sylow
    hcard (by omega) (by decide : Odd 3) A P hPA hP hnc Q hnQ

include hz hTV hTz hH hKH hK hgen in
/-- The G₂ root calculation identifies the intrinsic core of L₁-star. -/
theorem SourceHypothesis.original_abelian_normal_g2_star_core
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) :
    (actorImage H (D.fullSetup hZ T z).L₁).pCoreIn 2 =
      actorImage H ((T : Subgroup G) ⊓ K) := by
  have hle := S.original_abelian_normal_g2_point_le D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) (by omega))
  let e := (componentStarEquiv H K hKH hK).symm.trans
    (eK.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hcard))
  apply source_star_core_of_model S D hZ z hz hTV hTz hH hn e hle
  intro A P hA hPA hP hnc Q hnQ
  let _ := hA
  exact Atlas.G2.NoncyclicOddActor.twoCore_eq_sylow hq (by decide : Odd 3) A P hPA hP hnc Q hnQ
private theorem actorImage_core {H Y : Subgroup G} (hYH : Y ≤ H) :
    actorImage H (Y.pCoreIn 2) = (actorImage H Y).pCoreIn 2 := by
  have he : ((Y.subgroupOf H).pCoreIn 2).map H.subtype = Y.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hYH]
  have hi : (Y.pCoreIn 2).subgroupOf H = (Y.subgroupOf H).pCoreIn 2 := by
    rw [←he]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  change ((Y.pCoreIn 2).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) = _
  rw [hi,map_pCoreIn_of_ker_isPGroup (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)]
  rfl

include hTV hH in
/-- Lift the actual core equality through the entire ambient two-core. -/
theorem SourceHypothesis.original_sylow_intersection_le_edge_core_of_star_core
    (hs : (actorImage H (D.fullSetup hZ T z).L₁).pCoreIn 2 =
      actorImage H ((T : Subgroup G) ⊓ K)) :
    (T : Subgroup G) ⊓ K ≤ (D.fullSetup hZ T z).R₁ := by
  let E := D.fullSetup hZ T z
  let J := E.L₁ ⊔ (T : Subgroup G)
  have hJH : J ≤ H := sup_le (fun x hx => hH.1.2 (Or.inl hx))
    (fun x hx => hH.1.2 (Or.inr hx))
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hJH
  have hTL : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    (le_inf hTH hTV).trans
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  have hnL : J ≤ normalizer (E.L₁ : Set G) := sup_le E.L₁.le_normalizer hTL
  have hmcore : (actorImage H E.L₁).pCoreIn 2 ≤ (actorImage H J).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (map_mono (comap_mono le_sup_left))
      (by
        rintro _ ⟨x,hx,rfl⟩
        apply (E.L₁.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H))
        apply mem_map_of_mem
        rw [←subgroupOf_normalizer_eq (show E.L₁ ≤ H from fun x hx => hH.1.2 (Or.inl hx))]
        exact hnL hx)
  have himage : actorImage H ((T : Subgroup G) ⊓ K) ≤
      actorImage H E.R₁ := by
    rw [←hs]
    change _ ≤ actorImage H (J.pCoreIn 2)
    rw [actorImage_core hJH]
    exact hmcore
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using hh
  have hQR : H.pCoreIn 2 ≤ E.R₁ :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (hQT.trans le_sup_right)
      (hJH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  intro x hx
  let xH : H := ⟨x,hTH hx.1⟩
  have hmX : QuotientGroup.mk' (pCore 2 H) xH ∈ actorImage H E.R₁ :=
    himage (mem_map_of_mem _ hx)
  obtain ⟨y,hy,he⟩ := hmX
  have hxy : xH * y⁻¹ ∈ pCore 2 H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 H) (xH * y⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hmem := E.R₁.mul_mem (hQR (mem_map_of_mem H.subtype hxy)) hy
  change (x * y.val⁻¹) * y.val ∈ E.R₁ at hmem
  simpa only [inv_mul_cancel_right] using hmem

include hz hTV hTz hH hKH hK hgen in
/-- Both normal rank-two rows satisfy the source's original Sylow containment. -/
theorem SourceHypothesis.original_abelian_normal_rankTwo_sylow_le_edge_core
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ n) ∨
      Models.IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) :
    (T : Subgroup G) ⊓ K ≤ (D.fullSetup hZ T z).R₁ := by
  apply S.original_sylow_intersection_le_edge_core_of_star_core D hZ z hTV hH
  rcases hm with hm | hm
  · exact S.original_abelian_normal_symplectic_star_core D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  · exact S.original_abelian_normal_g2_star_core D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
end CFSG.Quasithin.Chapter12.Section06
