module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.Candidates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.PairGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders

/-!
# Common coordinates for the two covered source nodes

The literal L₀ and L₁,+ from Notation 13.2.1 have cubic two-core
quotients, calculated from the genuine covered natural action. Their
join L₁ has quotient of order nine. Restricting the actual Sylow of H*
to its normal component and using the prescribed component equivalence
gives the intrinsic common flag theorem exactly these two residuals.

The two distinct minimal parabolics are individually normalized by T*.
The source outer-action theorem therefore puts T* inside K*. Extending
that same component marking to all of H* retains the basis, ordered
nodes, both residuals and the two-node parabolic. No flag position,
residual identity or inner-action conclusion is an input hypothesis.
The earlier source factorization 13.2.2(3) remains explicit.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed pp.959–960 (PDF pp.976–977).
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open BinaryLinear.OuterCyclic
open BinaryLinear.InvariantNodeActions (minimalParabolic)
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction

private def inModel {X Y : Type*} [Group X] [Group Y] (K : Subgroup X)
    (e : K ≃* Y) (A : Subgroup X) : Subgroup Y :=
  (A.subgroupOf K).map e.toMonoidHom

private noncomputable def inModelEquiv {X Y : Type*} [Group X] [Group Y]
    (K A : Subgroup X) (e : K ≃* Y) (hA : A ≤ K) : A ≃* inModel K e A :=
  (subgroupOfEquivOfLe hA).symm.trans (e.subgroupMap (A.subgroupOf K))

private theorem inModel_card {X Y : Type*} [Group X] [Group Y]
    (K A : Subgroup X) (e : K ≃* Y) (hA : A ≤ K) :
    Nat.card (inModel K e A ⧸ pCore 2 (inModel K e A)) = Nat.card (A ⧸ pCore 2 A) := by
  let a := inModelEquiv K A e hA
  exact (Nat.card_congr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).toEquiv).symm

private theorem inModel_normalizes {X Y : Type*} [Group X] [Group Y]
    (K A B : Subgroup X) (e : K ≃* Y) (hn : A ≤ normalizer (B : Set X)) :
    inModel K e A ≤ normalizer (inModel K e B : Set Y) :=
  (map_mono ((comap_mono hn).trans (B.le_normalizer_comap K.subtype))).trans
    ((B.subgroupOf K).le_normalizer_map e.toMonoidHom)

private theorem inModel_sup {X Y : Type*} [Group X] [Group Y]
    (K A B : Subgroup X) (e : K ≃* Y) (hA : A ≤ K) (hB : B ≤ K) :
    inModel K e (A ⊔ B) = inModel K e A ⊔ inModel K e B := by
  rw [inModel, subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

variable {G : Type*} [Group G] [Finite G]

private theorem source_model_inputs (H K L T V₁ : Subgroup G)
    (hKH : K ≤ H) (hLK : one L T V₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hzero : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    {m : ℕ} (e : (K ⧸ pCore 2 K) ≃* PSL (m + 1)) :
    let f := linearModel (starLinearEquiv H K hKH hK e)
    let A := inModel (Source.starImage H K) f (Source.starImage H (zero L))
    let B := inModel (Source.starImage H K) f (Source.starImage H (plus L T V₁))
    ∃ U : Sylow 2 (LinearGroup (m + 1)),
      (U : Subgroup _) = inModel (Source.starImage H K) f
        (Source.starImage H T ⊓ Source.starImage H K) ∧
      IsPPerfect 2 A ∧ IsPPerfect 2 B ∧
      (U : Subgroup _) ≤ normalizer (A : Set (LinearGroup (m + 1))) ∧
      (U : Subgroup _) ≤ normalizer (B : Set (LinearGroup (m + 1))) ∧
      Nat.card (A ⧸ pCore 2 A) = 3 ∧ Nat.card (B ⧸ pCore 2 B) = 3 ∧
      Nat.card ((A ⊔ B : Subgroup _) ⧸ pCore 2 (A ⊔ B : Subgroup _)) = 9 := by
  dsimp only
  let C := Source.starImage H K
  let f := linearModel (starLinearEquiv H K hKH hK e)
  let A := Source.starImage H (zero L)
  let B := Source.starImage H (plus L T V₁)
  have h0K := (zero_le_one_of_factorization L T V₁ hfactor).trans hLK
  have hpK := (plus_le_one L T V₁ hTV).trans hLK
  have hAC : A ≤ C := map_mono (subgroupOf_mono H h0K)
  have hBC : B ≤ C := map_mono (subgroupOf_mono H hpK)
  let : C.Normal := by
    let := hKn
    exact Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _)
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS' : (S' : Subgroup (Source.Hstar H)) = Source.starImage H T := by
    change (S : Subgroup H).map _ = _
    rw [hS]
    rfl
  obtain ⟨U₀, hU₀⟩ := S'.exists_subgroupOf_eq_of_normal C
  let U : Sylow 2 (LinearGroup (m + 1)) := U₀.mapSurjective (f := f.toMonoidHom) f.surjective
  have hU : (U : Subgroup _) = inModel C f (Source.starImage H T ⊓ C) := by
    change (U₀ : Subgroup C).map f.toMonoidHom = _
    rw [hU₀, hS']
    congr 1
    ext x
    exact (and_iff_left x.property).symm
  have hperfect (D : Subgroup G) (hDH : D ≤ H) (hp : IsPPerfect 2 D)
      (hDC : Source.starImage H D ≤ C) : IsPPerfect 2 (inModel C f (Source.starImage H D)) := by
    have hp' := hp.of_surjective (starMap H D hDH) (starMap_surjective H D hDH)
    exact hp'.of_surjective (inModelEquiv C _ f hDC).toMonoidHom
      (inModelEquiv C _ f hDC).surjective
  have hcard (D : Subgroup G) (hDH : D ≤ H) (hDC : Source.starImage H D ≤ C) :
      Nat.card (inModel C f (Source.starImage H D) ⧸ pCore 2 (inModel C f (Source.starImage H D))) =
        Nat.card (D ⧸ pCore 2 D) :=
    (inModel_card C _ f hDC).trans
      (Nat.card_congr (starCoreQuotientEquiv H D hDH).toEquiv).symm
  refine ⟨U, hU, hperfect _ (h0K.trans hKH) (residual_isPPerfect _) hAC,
    hperfect _ (hpK.trans hKH) (residual_isPPerfect _) hBC, ?_, ?_,
    (hcard _ (h0K.trans hKH) hAC).trans hzero,
    (hcard _ (hpK.trans hKH) hBC).trans hplus, ?_⟩
  · rw [hU]
    exact inModel_normalizes C _ _ f
      (inf_le_left.trans (star_normalizes H T _ (hTL.trans (normalizer_le_zero_normalizer L))))
  · rw [hU]
    exact inModel_normalizes C _ _ f
      (inf_le_left.trans (star_normalizes H T _ (T_normalizes_plus L T V₁ hTL hTV)))
  · have hjoin : A ⊔ B = Source.starImage H (one L T V₁) := by
      conv_rhs => rw [hfactor, sup_comm]
      exact (congrArg (fun D : Subgroup H => D.map (QuotientGroup.mk' (pCore 2 H)))
        (subgroupOf_sup (h0K.trans hKH) (hpK.trans hKH))).trans (Subgroup.map_sup _ _ _)
        |>.symm
    rw [← inModel_sup C A B f hAC hBC, hjoin]
    exact (hcard _ (hLK.trans hKH) (map_mono (subgroupOf_mono H hLK))).trans
      (one_quotient_card L T V₁ hTL hTV hfactor hzero hplus)

private theorem small_common_coordinates {m : ℕ} (hm : m = 3 ∨ m = 4)
    (U : Sylow 2 (LinearGroup (m + 1))) (A B : Subgroup (LinearGroup (m + 1)))
    (ha : IsPPerfect 2 A) (hb : IsPPerfect 2 B)
    (hna : (U : Subgroup _) ≤ normalizer (A : Set (LinearGroup (m + 1))))
    (hnb : (U : Subgroup _) ≤ normalizer (B : Set (LinearGroup (m + 1))))
    (hca : Nat.card (A ⧸ pCore 2 A) = 3) (hcb : Nat.card (B ⧸ pCore 2 B) = 3)
    (hcab : Nat.card ((A ⊔ B : Subgroup _) ⧸ pCore 2 (A ⊔ B : Subgroup _)) = 9) :
    ∃ (b : Basis m) (i j : Fin m),
      (U : Subgroup _) = cutStabilizer b Set.univ ∧
      A ⊔ (U : Subgroup _) = minimalParabolic b i ∧
      B ⊔ (U : Subgroup _) = minimalParabolic b j ∧
      A = residual (minimalParabolic b i) ∧ B = residual (minimalParabolic b j) ∧
      (A ⊔ B) ⊔ (U : Subgroup _) = cutStabilizer b ({i,j} : Set (Fin m))ᶜ ∧
      i ≠ j ∧ (i.val + 1 < j.val ∨ j.val + 1 < i.val) := by
  rcases hm with rfl | rfl
  · obtain ⟨b, i, j, hu, hA, hB, hrA, hrB, hAB, hij, hgap, _⟩ :=
      PairGeometry.four_common_coordinates U A B ha hb hna hnb hca hcb hcab
    exact ⟨b, i, j, hu, hA, hB, hrA, hrB, hAB, hij, hgap⟩
  · obtain ⟨b, i, j, hu, hA, hB, hrA, hrB, hAB, hij, hgap, _⟩ :=
      PairGeometry.five_common_coordinates U A B ha hb hna hnb hca hcb hcab
    exact ⟨b, i, j, hu, hA, hB, hrA, hrB, hAB, hij, hgap⟩

/-- Extend the supplied component marking by the proved equality H* = K*.
The projective-to-linear comparison is the actual binary model equivalence. -/
noncomputable def wholeLinearModel (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ T = H) (hs : Source.starImage H T ≤ Source.starImage H K)
    {n : ℕ} [NeZero n] (e : (K ⧸ pCore 2 K) ≃* PSL n) :
    Source.Hstar H ≃* LinearGroup n :=
  (wholeStarLinearEquiv H K T hKH hTH hK hKT hs e).trans (pslEquivLinear n)

/-- Compatibility on every original component representative. -/
theorem wholeLinearModel_mk (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ T = H) (hs : Source.starImage H T ≤ Source.starImage H K)
    {n : ℕ} [NeZero n] (e : (K ⧸ pCore 2 K) ≃* PSL n) (k : K) :
    wholeLinearModel H K T hKH hTH hK hKT hs e
      (QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩) =
        pslEquivLinear n (e (QuotientGroup.mk' (pCore 2 K) k)) :=
  congrArg (pslEquivLinear n) (wholeStarLinearEquiv_mk H K T hKH hTH hK hKT hs e k)

private theorem whole_model_map (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ T = H) (hs : Source.starImage H T ≤ Source.starImage H K)
    {n : ℕ} [NeZero n] (e : (K ⧸ pCore 2 K) ≃* PSL n)
    (P : Subgroup (Source.Hstar H)) (hP : P ≤ Source.starImage H K) :
    P.map (wholeLinearModel H K T hKH hTH hK hKT hs e).toMonoidHom =
      inModel (Source.starImage H K) (linearModel (starLinearEquiv H K hKH hK e)) P := by
  conv_lhs => rw [← map_subgroupOf_eq_of_le hP, map_map]
  rfl

omit [Finite G] in
private theorem star_sup (H A B : Subgroup G) (hAH : A ≤ H) (hBH : B ≤ H) :
    Source.starImage H (A ⊔ B) = Source.starImage H A ⊔ Source.starImage H B := by
  rw [Source.starImage, subgroupOf_sup hAH hBH, Subgroup.map_sup]
  rfl

/-- The two marked source nodes in common coordinates. The cubic orders
are derived from the genuine covered natural action. Individual T*-invariance
and distinctness give T* ≤ K*; the same basis and ordered residuals then pass
to the extension of the originally supplied component marking. -/
theorem source_marked_pair (H K L T V V₁ V₃ : Subgroup G)
    (d : NaturalSetup L T V V₁ V₃)
    (hKH : K ≤ H) (hTH : T ≤ H) (hLK : one L T V₁ ≤ K)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (hKT : K ⊔ T = H)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    {m : ℕ} (hm : m = 3 ∨ m = 4) (e : (K ⧸ pCore 2 K) ≃* PSL (m + 1)) :
    ∃ (hs : Source.starImage H T ≤ Source.starImage H K)
      (b : Basis m) (i j : Fin m),
      i ≠ j ∧ (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
      candidate H K T (zero L) = ambientFlagStabilizer (starLinearEquiv H K hKH hK e)
        (deletedFlag (by omega : 2 ≤ m) b i) ∧
      candidate H K T (plus L T V₁) = ambientFlagStabilizer (starLinearEquiv H K hKH hK e)
        (deletedFlag (by omega : 2 ≤ m) b j) ∧
      candidate H K T (zero L) ≠ candidate H K T (plus L T V₁) ∧
      Source.starImage H T ≤ normalizer (candidate H K T (zero L) : Set (Source.Hstar H)) ∧
      Source.starImage H T ≤ normalizer (candidate H K T (plus L T V₁) : Set (Source.Hstar H)) ∧
      let eH := wholeLinearModel H K T hKH hTH hK hKT hs e
      (Source.starImage H T).map eH.toMonoidHom = cutStabilizer b Set.univ ∧
      (Source.starImage H (zero L)).map eH.toMonoidHom = residual (minimalParabolic b i) ∧
      (Source.starImage H (plus L T V₁)).map eH.toMonoidHom = residual (minimalParabolic b j) ∧
      (Source.starImage H (one L T V₁ ⊔ T)).map eH.toMonoidHom =
        cutStabilizer b ({i,j} : Set (Fin m))ᶜ := by
  let C := Source.starImage H K
  let f := linearModel (starLinearEquiv H K hKH hK e)
  let A := inModel C f (Source.starImage H (zero L))
  let B := inModel C f (Source.starImage H (plus L T V₁))
  have h0K := (zero_le_one_of_factorization L T V₁ hfactor).trans hLK
  have hpK := (plus_le_one L T V₁ d.line_stable).trans hLK
  have hAC : Source.starImage H (zero L) ≤ C := map_mono (subgroupOf_mono H h0K)
  have hBC : Source.starImage H (plus L T V₁) ≤ C := map_mono (subgroupOf_mono H hpK)
  obtain ⟨U, hU, ha, hb, hna, hnb, hca, hcb, hcab⟩ := source_model_inputs
    H K L T V₁ hKH hLK hK hKn d.normalizes_L d.line_stable hfactor
    d.zero_core_card (d.plus_core_card hfactor) S hS e
  obtain ⟨b, i, j, hu, hA, hB, hrA, hrB, hAB, hij, hgap⟩ :=
    small_common_coordinates hm U A B ha hb hna hnb hca hcb hcab
  have hnode (D : Subgroup G) (hDK : D ≤ K) (k : Fin m)
      (hcoord : inModel C f (Source.starImage H D) ⊔ (U : Subgroup _) = minimalParabolic b k) :
      candidate H K T D = ambientFlagStabilizer (starLinearEquiv H K hKH hK e)
        (deletedFlag (by omega : 2 ≤ m) b k) := by
    apply ambient_eq_of_linear_image _ (candidate_le_component H K T D hDK)
    rw [deletedFlag_stabilizer, map_comap_eq_self_of_surjective f.surjective]
    change inModel C f (candidate H K T D) = _
    change inModel C f (Source.starImage H D ⊔ (Source.starImage H T ⊓ C)) = _
    rw [inModel_sup C (Source.starImage H D) (Source.starImage H T ⊓ C) f
      (map_mono (subgroupOf_mono H hDK)) inf_le_right, ← hU]
    exact hcoord
  have hP := hnode (zero L) h0K i hA
  have hQ := hnode (plus L T V₁) hpK j hB
  have ht : IsPGroup 2 T := by
    have ht := S.isPGroup'.map H.subtype
    rwa [hS, map_subgroupOf_eq_of_le hTH] at ht
  have hs := inner_of_candidate_flags H K L T V₁ hKH hTH hK hKn hKT (hLK.trans hKH)
    ht d.normalizes_L d.line_stable hcover hfactor (d.plus_core_card hfactor) S hS
    (by omega : 2 ≤ m) (by omega : m ≤ 4) e b b i j hP hQ
  have hTK := hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
  refine ⟨hs, b, i, j, hij, hgap, hP, hQ,
    candidates_ne H K L T V₁ (hLK.trans hKH) ht d.normalizes_L d.line_stable
      hcover hfactor (d.plus_core_card hfactor),
    candidate_normalized H K T (zero L) hTK
      (d.normalizes_L.trans (normalizer_le_zero_normalizer L)),
    candidate_normalized H K T (plus L T V₁) hTK
      (T_normalizes_plus L T V₁ d.normalizes_L d.line_stable), ?_⟩
  dsimp only
  have hwhole (D : Subgroup (Source.Hstar H)) (hD : D ≤ C) :=
    whole_model_map H K T hKH hTH hK hKT hs e D hD
  have hTimage : (Source.starImage H T).map
      (wholeLinearModel H K T hKH hTH hK hKT hs e).toMonoidHom = (U : Subgroup _) := by
    rw [hwhole _ hs, hU]
    rw [inf_eq_left.mpr hs]
  refine ⟨hTimage.trans hu, (hwhole _ hAC).trans hrA, (hwhole _ hBC).trans hrB, ?_⟩
  rw [star_sup H _ T (hLK.trans hKH) hTH, Subgroup.map_sup, hTimage]
  conv_lhs => rw [hfactor]
  rw [star_sup H _ _ (hpK.trans hKH) (h0K.trans hKH), Subgroup.map_sup, hwhole _ hBC, hwhole _ hAC]
  exact (congrArg (fun D : Subgroup (LinearGroup (m + 1)) => D ⊔ U) (sup_comm B A)).trans hAB


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource
end
