module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCorePoint
public import Theory.GroupTheory.PGroup.SupercriticalCubic
public import Theory.GroupTheory.SmallFittingResidual

/-!
# The actual point and the selected supercritical three-core lift

For an extraspecial supercritical subgroup, every ambient order-three
root belongs to that subgroup. Apply this to the original cubic point
image inside O₃(J/O₂(J)). Two-perfectness then lifts its containment
through the full two-core to the selected normal lift Y. Consequently
O₂(Y) is properly contained in Y ∩ N_G(L), with both subgroups transported
to the original ambient group. This is the literal intersection premise
used in source 14.7.9.

In the elementary-nine branch, if the point cubic is outside the selected
supercritical image, its centralizer there is a proper nontrivial cubic.
Take a two-perfect lift inside the same Y. It is proper in Y, normalized
by L₁T and by the whole O₂(J), and its quotient map has exactly O₂(W)
as kernel. Its commutator with L₁ lies in O₂(J).

The final application constructs these alternatives on the original
selected witnesses, retaining the elementary-nine residual equality and
all quotient markings. Ambient 14.7.9 and the minimality exclusions are
still needed; this does not assert nonsolvability or finish 14.7.52.

Source: Aschbacher–Smith, A.1.20–23, printed pp.24–25; 14.7.9,
printed p.1045; 14.7.27, printed pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem local_point_le_normal_three_lift
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (him : ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      Y.map (QuotientGroup.mk' (pCore 2 J))) : (F.Li L 1).subgroupOf J ≤ Y := by
  let q := QuotientGroup.mk' (pCore 2 J)
  have hp : IsPPerfect 2 ((F.Li L 1).subgroupOf J) := by
    have hp₀ : IsPPerfect 2 (F.Li L 1) := by
      simp only [InvariantFlag.Li]
      exact isPPerfect_embedded_pResidual 2 _
    let e := (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)).symm
    exact hp₀.of_surjective e.toMonoidHom e.surjective
  apply twoPerfect_le_of_le_sup_twoGroup Y _ q.ker hp
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  rw [←comap_map_eq]
  exact map_le_iff_le_comap.mp him

/-- Every point cubic in the Heisenberg branch lies in the actual supercritical image. -/
theorem local_solvable_heisenberg_point_le_supercritical
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* HeisenbergPrime 3) :
    ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      X.map (pCore 3 (HStar J)).subtype := by
  let : IsExtraspecial 3 X := IsExtraspecial.of_mulEquiv e.symm
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2))
  let B := ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
  have hc : Nat.card B = 3 := (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have hBP := local_solvable_point_le_threeCore h hab structural previous faithful J hJ hs
  intro b hb
  have hb3 : b ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨b,hb⟩ : B))
    rw [hc] at hh
    exact congrArg Subtype.val hh
  exact mem_map_of_mem (pCore 3 (HStar J)).subtype
    (hX.prime_root_mem_of_extraspecial (⟨b,hBP hb⟩ : pCore 3 (HStar J)) (Subtype.ext hb3))

/-- Point containment lifts through the whole two-core to every selected normal Heisenberg lift. -/
theorem local_solvable_heisenberg_point_le_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* HeisenbergPrime 3) (Y : Subgroup J) [Y.Normal]
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype) :
    (F.Li L 1).subgroupOf J ≤ Y := by
  apply local_point_le_normal_three_lift J hJ Y
  rw [hm]
  exact local_solvable_heisenberg_point_le_supercritical h hab structural previous faithful J hJ hs X hX e

/-- In the elementary-nine branch an outside point cubic gives an actual proper cubic lift,
normalized by the original point parabolic and the full quotient kernel. -/
theorem local_solvable_nine_outside_point_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (Y : Subgroup J) [Y.Normal]
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype)
    (hout : ¬ ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      X.map (pCore 3 (HStar J)).subtype) :
    ∃ W : Subgroup J, W < Y ∧ IsPPerfect 2 W ∧
      W.map (QuotientGroup.mk' (pCore 2 J)) =
        X.map (pCore 3 (HStar J)).subtype ⊓
          centralizer (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) : Set (HStar J)) ∧
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J) ≤ normalizer (W : Set J) ∧
      pCore 2 J ≤ normalizer (W : Set J) ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = pCore 2 W ∧
      Nat.card (W ⧸ pCore 2 W) = 3 ∧
      ⁅W,(F.Li L 1).subgroupOf J⁆ ≤ pCore 2 J := by
  let P := pCore 3 (HStar J)
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := ((F.Li L 1).subgroupOf J).map q
  let Z := X.map P.subtype
  let C := Z ⊓ centralizer (B : Set (HStar J))
  let A := (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J
  have hcard : Nat.card X = 9 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hne : X ≠ ⊥ := by intro he; simp [he] at hcard
  have hB : Nat.card B = 3 := (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have hBP := local_solvable_point_le_threeCore h hab structural previous faithful J hJ hs
  obtain ⟨hCne,hCZ,hCN⟩ := hX.cubic_centralizer_proper P pCore_isPGroup X B hBP hB hne hout
  have hCsmall : Nat.card C = 3 := by
    have hh := (hX.cubic_centralizer_elementary P pCore_isPGroup X B hBP hB (Or.inl hcard) hout).2
    apply hh.resolve_right
    intro he
    apply hCZ.ne
    exact eq_of_le_of_card_ge inf_le_left (by rw [he,card_map_of_injective P.subtype_injective,hcard])
  have hAN : A ≤ normalizer ((F.Li L 1).subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    intro x hx
    exact (sup_le (F.Li L 1).le_normalizer (T_normalizes_L₁ h structural)) hx
  have hAC : A.map q ≤ normalizer (C : Set (HStar J)) :=
    ((map_mono hAN).trans (le_normalizer_map q)).trans hCN
  obtain ⟨W,hWY,hWp,hWm,hWA,hWk,hker,⟨eW⟩⟩ := exists_three_lift_within_normal q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) Y C (A.map q)
    (hm.symm ▸ inf_le_left) hAC (IsPGroup.of_card (n := 1) (by simpa using hCsmall))
  refine ⟨W,lt_of_le_of_ne hWY ?_,hWp,hWm,(le_comap_map _ _).trans hWA,(by simpa only [q,QuotientGroup.ker_mk'] using hWk),hker,
    (Nat.card_congr eW.toEquiv).trans hCsmall,?_⟩
  · intro he
    apply hCZ.ne
    calc C = W.map q := hWm.symm
         _ = Y.map q := congrArg (map q) he
         _ = Z := hm
  · rw [←QuotientGroup.ker_mk' (pCore 2 J),←Subgroup.map_eq_bot_iff,map_commutator,hWm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right


/-- A normal lift containing the point residual has the strict normalizer intersection
required in 14.7.9, with the intrinsic two-core retained. -/
private theorem local_solvable_lift_point_intersection_relative
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hpoint : (F.Li L 1).subgroupOf J ≤ Y) :
    Y.pCoreIn 2 < Y ⊓ (normalizer (L : Set G)).subgroupOf J := by
  have hcore : Y.pCoreIn 2 ≤ pCore 2 J :=
    le_sSup ⟨inferInstanceAs (((pCore 2 Y).map Y.subtype).Normal),pCore_isPGroup.map Y.subtype⟩
  let S := T.subtype (show (T : Subgroup G) ≤ J from fun x hx => hJ.1.2 (Or.inr hx))
  have hCM : Y.pCoreIn 2 ≤ (normalizer (L : Set G)).subgroupOf J := by
    intro x hx
    exact h.sylow_normalizes structural ((pCore_isPGroup.le_sylow_of_normal S) (hcore hx))
  have hAM : (F.Li L 1).subgroupOf J ≤ (normalizer (L : Set G)).subgroupOf J := by
    intro x hx
    exact L.le_normalizer ((F.Li_le L 1 hx).1)
  refine lt_of_le_of_ne (le_inf (pCoreIn_le 2 Y) hCM) ?_
  intro he
  have hAcore : (F.Li L 1).subgroupOf J ≤ Y.pCoreIn 2 :=
    (le_inf hpoint hAM).trans_eq he.symm
  have hz : ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hAcore.trans hcore
  have hc := (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  rw [hz,card_bot] at hc
  omega


/-- The strict 14.7.9 intersection, transported to the original ambient group
and its literal normalizer; the core is the lift's intrinsic two-core. -/
theorem local_solvable_lift_point_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hpoint : (F.Li L 1).subgroupOf J ≤ Y) :
    (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G) := by
  have hh := local_solvable_lift_point_intersection_relative
    h hab structural previous faithful J hJ hs Y hpoint
  have hm := lt_of_le_of_ne (map_mono (f := J.subtype) hh.le)
    (fun he => hh.ne (map_injective J.subtype_injective he))
  have hi : (Y ⊓ (normalizer (L : Set G)).subgroupOf J).map J.subtype =
      Y.map J.subtype ⊓ normalizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨mem_map_of_mem J.subtype hy.1,hy.2⟩
    · rintro ⟨⟨y,hy,rfl⟩,hyM⟩
      exact ⟨y,⟨hy,hyM⟩,rfl⟩
  rwa [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,hi] at hm

private def selectedLiftModel (J : Subgroup G)
    (X : Subgroup (pCore 3 (HStar J))) (Y : Subgroup J)
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype)
    (hk : ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y) :
    (Y ⧸ pCore 2 Y) ≃* X := by
  let f := (QuotientGroup.mk' (pCore 2 J)).comp Y.subtype
  have hr : f.range = X.map (pCore 3 (HStar J)).subtype := by
    rw [MonoidHom.range_comp,range_subtype,hm]
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      ((MulEquiv.subgroupCongr hr).trans
        (equivMapOfInjective X (pCore 3 (HStar J)).subtype
          (pCore 3 (HStar J)).subtype_injective).symm))

/-- On the original selected lifts, Heisenberg forces the strict point intersection.
The elementary-nine alternative either has the same intersection or an actual
proper cubic lift centralizing the point modulo precisely the full two-core. -/
theorem local_solvable_threeCore_lift_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar J) = pCore 3 (HStar J) ∧
          (((F.Li L 1).subgroupOf J ≤ Y ∧
              (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) ∨
            ∃ W : Subgroup J, W < Y ∧ IsPPerfect 2 W ∧
              W.map (QuotientGroup.mk' (pCore 2 J)) =
                X.map (pCore 3 (HStar J)).subtype ⊓
                  centralizer (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) : Set (HStar J)) ∧
              ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J) ≤ normalizer (W : Set J) ∧
              pCore 2 J ≤ normalizer (W : Set J) ∧
              ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = pCore 2 W ∧
              Nat.card (W ⧸ pCore 2 W) = 3 ∧
              ⁅W,(F.Li L 1).subgroupOf J⁆ ≤ pCore 2 J)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          (F.Li L 1).subgroupOf J ≤ Y ∧
          (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G))) := by
  obtain ⟨_,_,X,hX,Y,hYn,hYp,hYle,hm,hk,he⟩ :=
    local_solvable_threeCore_point_reduction h hab structural previous faithful J hJ hs
  let := hYn
  let e := selectedLiftModel J X Y hm hk
  refine ⟨X,hX,Y,hYn,hYp,hYle,hm,hk,?_⟩
  rcases he with ⟨he,hr⟩ | he
  · refine Or.inl ⟨he,hr,?_⟩
    by_cases hb : ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
        X.map (pCore 3 (HStar J)).subtype
    · have hpoint := local_point_le_normal_three_lift J hJ Y (hm.symm ▸ hb)
      exact Or.inl ⟨hpoint,local_solvable_lift_point_intersection
        h hab structural previous faithful J hJ hs Y hpoint⟩
    · exact Or.inr (local_solvable_nine_outside_point_lift h hab structural previous faithful
        J hJ hs X hX (e.symm.trans he.some) Y hm hb)
  · have hpoint := local_solvable_heisenberg_point_le_lift h hab structural previous faithful
      J hJ hs X hX (e.symm.trans he.some) Y hm
    exact Or.inr ⟨he,hpoint,local_solvable_lift_point_intersection
      h hab structural previous faithful J hJ hs Y hpoint⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
