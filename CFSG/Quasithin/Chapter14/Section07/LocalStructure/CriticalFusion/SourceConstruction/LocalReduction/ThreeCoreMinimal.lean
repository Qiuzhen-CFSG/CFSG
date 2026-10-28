module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreAmbient
public import Theory.GroupTheory.CubicFixedLineOvergroup

/-!
# Minimal solvable locals and the strict source intersection

Choose a minimal escaping solvable overgroup of the original L₁T. Every
proper subgroup between L₁T and this witness lies in M = N_G(L). In the
outside-point elementary-nine branch, the actual cubic fixed-line lift
and L₁T generate a proper subgroup: otherwise its three-core would have
order at most nine and contain both the selected nine-group and the
outside point. Minimality therefore places this cubic lift in M.

Its nontrivial image through the full O₂(J) kernel gives
O₂(Y) < Y ∩ M for the selected normal lift Y. The other elementary-nine
case and the Heisenberg case already have this intersection by point
containment. The final theorem constructs the minimal witness and all
markings from the original hypotheses, so the intersection now holds in
every remaining solvable branch. It also retains the proper normal
cubic-center lift and ambient commutator obstruction in the Heisenberg case.

The ambient restriction 14.7.9 and terminal exclusions remain required;
this does not assert nonsolvability or the four final Data inputs.
Source: Aschbacher–Smith, 14.7.9 and 14.7.27–29, printed pp.1045,
1054–1055, refs/quasithin.pdf.
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

/-- Choose an actual minimal escaping solvable local subgroup. Every proper
overgroup of the original point parabolic inside it lies in M. -/
theorem exists_minimal_solvable_local
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      ∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G) := by
  obtain ⟨I,⟨hI,hIs⟩,hIJ,hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun D : Subgroup G => D ∈ F.Hz L (normalizer (L : Set G)) ∧ Group.IsSolvable D)
    J ⟨hJ,hs⟩
  refine ⟨I,hIJ,hI,hIs,?_⟩
  intro D hBD hDI
  by_contra hout
  have hc : Nat.card (F.Vi 1) = 2 := F.card 1 (by decide)
  have hpoint : F.Vi 1 ≤ D.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 1) (by simpa using hc))
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans hBD)))
    (hDI.le.trans hI.2.1)
  have hcore : D.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hz := le_bot_iff.mp (he ▸ hpoint)
    rw [hz,card_bot] at hc
    omega
  have hD : D ∈ F.Hz L (normalizer (L : Set G)) :=
    ⟨⟨hcore,fun _ hx => hx.elim (fun ha => hBD (mem_sup_left ha))
      (fun ha => hBD (mem_sup_right ha))⟩,hDI.le.trans hI.2.1,hout⟩
  let := hIs
  have hDs : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hDI.le) (inclusion_injective hDI.le)
  exact hDI.ne (hmin D ⟨hD,hDs⟩ hDI.le)

/-- The actual outside-point cubic lift and original point parabolic generate
a proper subgroup of J, with the full two-core retained. -/
theorem local_solvable_nine_cubic_join_proper
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J)))
    (hX : Nat.card X = 9)
    (hout : ¬ ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      X.map (pCore 3 (HStar J)).subtype)
    (W : Subgroup J)
    (hm : W.map (QuotientGroup.mk' (pCore 2 J)) =
      X.map (pCore 3 (HStar J)).subtype ⊓
        centralizer (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) : Set (HStar J)))
    (hWN : ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J) ≤ normalizer (W : Set J))
    (hk : ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = pCore 2 W)
    (hc : Nat.card (W ⧸ pCore 2 W) = 3) :
    W.map J.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) < J := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let P := pCore 3 (HStar J)
  let B := (F.Li L 1).subgroupOf J
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  have hBN : (S : Subgroup J) ≤ normalizer (B : Set J) := by
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    intro x hx
    exact T_normalizes_L₁ h structural hx
  have hCW : Nat.card (W.map q) = 3 := by
    let f := q.comp W.subtype
    have hr : f.range = W.map q := by rw [MonoidHom.range_comp,range_subtype]
    rw [←hr,←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hk]
    exact hc
  have hnorm : (S : Subgroup J) ≤ normalizer (W : Set J) :=
    (show (S : Subgroup J) ≤ (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J from
      fun x hx => mem_sup_right hx).trans hWN
  have hne := cubic_fixed_line_join_ne_top (X.map P.subtype) (B.map q) (W.map q)
    ((S : Subgroup J).map q)
    ((card_map_of_injective P.subtype_injective).trans hX) (map_subtype_le X)
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2 hCW
    ((le_centralizer_iff.mp (hm ▸ inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)) hout
    (S.isPGroup'.map q) ((map_mono hBN).trans (le_normalizer_map q))
    ((map_mono hnorm).trans (le_normalizer_map q))
  let D := W ⊔ B ⊔ (S : Subgroup J)
  have hDne : D ≠ ⊤ := by
    intro he
    apply hne
    rw [←Subgroup.map_sup,←Subgroup.map_sup,show W ⊔ B ⊔ (S : Subgroup J) = D from rfl,he,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hmap : D.map J.subtype = W.map J.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) := by
    rw [show D = W ⊔ B ⊔ (S : Subgroup J) from rfl,Subgroup.map_sup,Subgroup.map_sup,
      map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hJ),Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ),sup_assoc]
  rw [←hmap]
  exact lt_of_le_of_ne (map_subtype_le D) (fun he => hDne
    (map_injective J.subtype_injective (by simpa only [←MonoidHom.range_eq_map,range_subtype] using he)))

/-- Minimality places the actual outside-point cubic lift in M. This is the
proper-centralizer step of 14.7.27 on the original local and quotient map. -/
theorem local_minimal_solvable_nine_outside_point_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (hmin : ∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < J →
      D ≤ normalizer (L : Set G))
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
      ⁅W,(F.Li L 1).subgroupOf J⁆ ≤ pCore 2 J ∧
      W.map J.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) < J ∧
      W.map J.subtype ≤ normalizer (L : Set G) := by
  obtain ⟨W,hWY,hWp,hWm,hWA,hWQ,hWk,hWc,hWB⟩ := local_solvable_nine_outside_point_lift
    h hab structural previous faithful J hJ hs X hX e Y hm hout
  have hcX : Nat.card X = 9 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hproper := local_solvable_nine_cubic_join_proper h hab structural previous faithful
    J hJ hs X hcX hout W hWm hWA hWk hWc
  exact ⟨W,hWY,hWp,hWm,hWA,hWQ,hWk,hWc,hWB,hproper,
    le_sup_left.trans (hmin _ le_sup_right hproper)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A cubic sublift lying in M makes the original normal lift meet M beyond
its own two-core. The kernel used to detect nontriviality is the whole O₂(J). -/
theorem local_lift_intersection_of_cubic_sublift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal] (W : Subgroup J) (hWY : W ≤ Y)
    (hWM : W.map J.subtype ≤ normalizer (L : Set G))
    (hk : ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = pCore 2 W)
    (hc : Nat.card (W ⧸ pCore 2 W) = 3) :
    (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G) := by
  have hcore : Y.pCoreIn 2 ≤ pCore 2 J :=
    le_sSup ⟨inferInstanceAs (((pCore 2 Y).map Y.subtype).Normal),pCore_isPGroup.map Y.subtype⟩
  have hQJ : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow J (T.subtype (F.sylow_le_of_mem_Hz hJ))
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ)] at hh
  have hQM : (Y.map J.subtype).pCoreIn 2 ≤ normalizer (L : Set G) := by
    rw [←map_pCoreIn_of_injective 2 Y J.subtype J.subtype_injective]
    exact (map_mono hcore).trans (hQJ.trans (h.sylow_normalizes structural))
  refine lt_of_le_of_ne (le_inf (pCoreIn_le 2 _) hQM) ?_
  intro he
  have hWcore : W.map J.subtype ≤ (Y.map J.subtype).pCoreIn 2 :=
    (le_inf (map_mono hWY) hWM).trans_eq he.symm
  rw [←map_pCoreIn_of_injective 2 Y J.subtype J.subtype_injective] at hWcore
  have hWQ : W ≤ pCore 2 J :=
    ((map_le_map_iff_of_injective J.subtype_injective).mp hWcore).trans hcore
  have hktop : ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = ⊤ := by
    apply top_unique
    intro w _
    change QuotientGroup.mk' (pCore 2 J) (w : J) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hWQ w.property)
  rw [←hk,hktop] at hc
  have hone : Nat.card (W ⧸ (⊤ : Subgroup W)) = 1 := by
    rw [←index_eq_card,index_top]
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Original solvable locals supply a minimal witness with the ambient
normalizer obstruction and the proper-lift minimality step discharged.
The contained-point and normal-center exclusions remain to be proved. -/
theorem local_minimal_solvable_threeCore_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (¬ ⁅L,Y.map I.subtype⁆ ≤ L.pCoreIn 2) ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          (F.Li L 1).subgroupOf I ≤ Y ∧
          ∃ Z : Subgroup I, Z < Y ∧ Z.Normal ∧ IsPPerfect 2 Z ∧
            Z.map (QuotientGroup.mk' (pCore 2 I)) =
              ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype ∧
            ((QuotientGroup.mk' (pCore 2 I)).comp Z.subtype).ker = pCore 2 Z ∧
            Nat.card (Z ⧸ pCore 2 Z) = 3 ∧ Nonempty ((Z ⧸ pCore 2 Z) ≃* center X) ∧
            pCore 2 Z ≠ ⊥ ∧ ¬ ⁅L,Z.map I.subtype⁆ ≤ L.pCoreIn 2)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin⟩ := exists_minimal_solvable_local h J hJ hs
  obtain ⟨X,hX,Y,hYn,hYp,hYr,hm,hk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful I hI hIs
  let := hYn
  let eX : (Y ⧸ pCore 2 Y) ≃* X := (coreQuotientEquivImage 2 Y).trans
    ((MulEquiv.subgroupCongr hm).trans
      (equivMapOfInjective X (pCore 3 (HStar I)).subtype
        (pCore 3 (HStar I)).subtype_injective).symm)
  have hYne : Y ≠ ⊥ := by
    intro hz
    have hone : Nat.card (Y ⧸ pCore 2 Y) = 1 := by
      have hd := card_quotient_dvd_card (pCore 2 Y)
      have hcardY : Nat.card Y = 1 := by rw [hz,card_bot]
      rw [hcardY] at hd
      exact Nat.dvd_one.mp hd
    rcases he with he | he
    · rw [Nat.card_congr he.some.toEquiv,Nat.card_prod] at hone
      norm_num [Nat.card_zmod] at hone
    · rw [Nat.card_congr he.some.toEquiv,HeisenbergPrime.card] at hone
      norm_num at hone
  refine ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,
    local_normal_twoPerfect_not_core_commutator h structural I hI Y hYp hYne,?_⟩
  rcases he with he | he
  · let e := eX.symm.trans he.some
    have hr := local_solvable_nine_residual_eq_threeCore h hab structural previous faithful
      I hI hIs X hX e
    by_cases hpoint : (F.Li L 1).subgroupOf I ≤ Y
    · exact ⟨local_solvable_lift_point_intersection
        h hab structural previous faithful I hI hIs Y hpoint,Or.inl ⟨he,hr⟩⟩
    · have hout : ¬ ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
          X.map (pCore 3 (HStar I)).subtype := by
        intro hh
        apply hpoint
        have hp : IsPPerfect 2 ((F.Li L 1).subgroupOf I) := by
          have hp₀ : IsPPerfect 2 (F.Li L 1) := by
            simp only [InvariantFlag.Li]
            exact isPPerfect_embedded_pResidual 2 _
          let e₀ := (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hI)).symm
          exact hp₀.of_surjective e₀.toMonoidHom e₀.surjective
        apply twoPerfect_le_of_le_sup_twoGroup Y _ (pCore 2 I) hp pCore_isPGroup
        rw [←QuotientGroup.ker_mk' (pCore 2 I),←comap_map_eq]
        exact map_le_iff_le_comap.mp (hm.symm ▸ hh)
      obtain ⟨W,hWY,_,_,_,_,hWk,hWc,_,_,hWM⟩ :=
        local_minimal_solvable_nine_outside_point_lift h hab structural previous faithful
          I hI hIs hmin X hX e Y hm hout
      exact ⟨local_lift_intersection_of_cubic_sublift h structural I hI Y W hWY.le hWM hWk hWc,Or.inl ⟨he,hr⟩⟩
  · let e := eX.symm.trans he.some
    have hpoint := local_solvable_heisenberg_point_le_lift h hab structural previous faithful
      I hI hIs X hX e Y hm
    exact ⟨local_solvable_lift_point_intersection h hab structural previous faithful I hI hIs Y hpoint,
      Or.inr ⟨he,hpoint,local_solvable_heisenberg_center_lift h structural I hI X hX e Y hm⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
