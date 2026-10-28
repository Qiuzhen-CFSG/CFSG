module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourPlaneLattice
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneResidual
public import Theory.GroupAction.TwoTransitiveFactorization
public import Theory.SpecificGroups.FifteenPointSubgroups.Actions
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.PairJoin
public import Theory.Quasithin.NormalTwoQuotient
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# Plane control in the mixed PSL₅(2) point row

The original module has degree four while K₁/O₂(K₁) is PSL₅(2).
The point parabolic L₁T has three-rank one, by its normal two-extension
of L₁ and the literal GL₃(2) core quotient. If the plane bound fails,
Y and L₁T lie strictly above their common last-node parabolic. The binary
flag lattice identifies H/O₂(H) with GL₄(2), where H is the actual join
Y join L₁, without identifying H with the whole K₁T.

The already identified quotient Y/O₂(Y) is GL₃(2). The two-transitive
coset action in H/O₂(H) therefore factors every element outside Y into
one double coset. For R=O²(Y), the span E=⟨V^R⟩ is Y-invariant; a
representative in L₁ preserves V, so E contains every H-conjugate of V₂.
The original L₁ irreducibility gives U_H=E, contradicting the proved
I₂-normalization obstruction on the same flag. This proves the plane
centralizer bound and all LocalControl clauses in the mixed row.

The endpoint NaturalSource applies these results to construct the same-flag
terminal configuration. The A₇ plane bound and corrected nonabelian
catalogue remain with that assembly. Source: Aschbacher--Smith,
refs/quasithin.pdf, 12.9.7, printed p.862 (PDF p.879).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original degree-four point parabolic has cubic rank one. -/
theorem four_point_parabolic_three_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) :
    primeRank 3 (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ≤ 1 := by
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let N := (F.Li L 1).subgroupOf B
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le (F.Li L 1).le_normalizer (sylow_normalizes_point_residual h earlier F))
  have hquot : IsPGroup 2 (B ⧸ N) := by
    apply isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf B) T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup (show F.Li L 1 ≤ B from le_sup_left)
      (show (T : Subgroup G) ≤ B from le_sup_right),subgroupOf_self]
  rw [primeRank_eq_of_normal_two_quotient N hquot 3 (by decide),
    primeRank_equiv 3 (subgroupOfEquivOfLe (show F.Li L 1 ≤ B from le_sup_left)),
    ←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 (F.Li L 1)) pCore_isPGroup]
  apply primeRank_le_one_of_square_not_dvd
  rw [Nat.card_congr (Components.Li_three_core_equiv h F 1
    (Or.inr ⟨rfl,Or.inl rfl⟩) rfl).some.toEquiv,Atlas.Comparisons.Exceptional.sl3Two_card]
  decide

/-- Failure of the plane bound in the mixed row gives the actual GL₄(2)
quotient of H=Y join L₁, rather than identifying H with the whole K₁T. -/
theorem four_mixed_plane_escape_join_equiv
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hfail : ¬ centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) :
    let H := planeCentralizerJoin F C ⊔ F.Li L 1
    Nonempty ((H ⧸ pCore 2 H) ≃* LinearGroup 4) := by
  let := h.chosen.elementary
  let X := C.K1 ⊔ (T : Subgroup G)
  let Y := planeCentralizerJoin F C
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let J := F.orderedParabolic L 3
  let H := Y ⊔ F.Li L 1
  have hYX : Y ≤ X := inf_le_left
  have hBX : B ≤ X := sup_le_sup_right C.contains _
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTY : (T : Subgroup G) ≤ Y := (planeCentralizerJoin_placements h F C).1
  obtain ⟨hTJ,hJY⟩ := four_plane_escape_chain h earlier F hab C hfail
  have hJH := F.orderedParabolic_le_H (by decide : 2 ≤ 4) L (by decide : 2 ≤ 3)
  have hJB : J ≤ B := by
    change F.orderedParabolic L 3 ≤ F.Li L 1 ⊔ (T : Subgroup G)
    rw [Components.point_residual_sylow_eq_intersection h earlier F]
    exact le_inf inf_le_left hJH
  have hJG : J ≤ F.Gi 2 :=
    inf_le_right.trans (iInf_le_of_le 2 (iInf_le_of_le (by decide) le_rfl))
  have hLnot : ¬ F.Li L 1 ≤ F.Gi 2 := by
    intro hL
    rcases F.localKernel_irreducible L (by decide : 2 ≤ 4) h.chosen.normalizes
      (fun _ => ⟨h.naturalMarking⟩) (F.Vi 2) (F.monotone (by decide)) (F.le_seed 2) hL with he | he
    · have hh := congrArg (fun A : Subgroup G => Nat.card A) he
      rw [F.card 2 (by decide),F.card 1 (by decide)] at hh
      norm_num at hh
    · have hh := congrArg (fun A : Subgroup G => Nat.card A) (he.trans F.last.symm)
      rw [F.card 2 (by decide),F.card 4 (by decide)] at hh
      norm_num at hh
  have hJB' : J < B := lt_of_le_of_ne hJB (fun he =>
    hLnot (le_sup_left.trans (he.ge.trans hJG)))
  have hne : Y ≠ B := fun he =>
    (plane_centralizer_escape_join h (Or.inl rfl) earlier F hab C hfail).1 he.le
  obtain ⟨eX⟩ := four_point_join_binary_equiv h earlier F C (Or.inr rfl) hm
  let q := eX.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := eX.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eX.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hJX : J ≤ X := hJY.le.trans hYX
  have hstrict {A D : Subgroup G} (hAX : A ≤ X) (hDX : D ≤ X) (hAD : A < D) :
      A.subgroupOf X < D.subgroupOf X := lt_of_le_of_ne (comap_mono hAD.le) (fun he => by
    have hh := congrArg (map X.subtype) he
    rw [map_subgroupOf_eq_of_le hAX,map_subgroupOf_eq_of_le hDX] at hh
    exact hAD.ne hh)
  have hneq : Y.subgroupOf X ≠ B.subgroupOf X := fun he => by
    have hh := congrArg (map X.subtype) he
    rw [map_subgroupOf_eq_of_le hYX,map_subgroupOf_eq_of_le hBX] at hh
    exact hne hh
  have hrY : primeRank 3 (Y.subgroupOf X) ≤ 1 := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hYX)]
    exact planeCentralizerJoin_three_rank h (Or.inl rfl) earlier F hab C
  have hrB : primeRank 3 (B.subgroupOf X) ≤ 1 := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hBX)]
    exact four_point_parabolic_three_rank h earlier F
  obtain ⟨a⟩ := BinaryLinear.SylowFlagOvergroups.five_pair_join_quotient_of_two_kernel
    q hq hk (T.subtype hTX) (J.subgroupOf X) (Y.subgroupOf X) (B.subgroupOf X)
    (hstrict hTX hJX hTJ) (hstrict hJX hYX hJY) (hstrict hJX hBX hJB') hneq hrY hrB
  have hjoin : Y ⊔ B = H := by
    change Y ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = Y ⊔ F.Li L 1
    rw [←sup_assoc,sup_eq_left.mpr (hTY.trans le_sup_left)]
  rw [←subgroupOf_sup hYX hBX,hjoin] at a
  have hHX : H ≤ X := sup_le hYX (C.contains.trans le_sup_left)
  let c := subgroupOfEquivOfLe hHX
  exact ⟨(QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.trans a⟩

/-- The source plane bound for the original mixed PSL₅(2) point-component quotient. -/
theorem four_plane_bound_of_binary_five
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) :
    centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) := by
  classical
  by_contra hfail
  let := h.chosen.elementary
  let Y := planeCentralizerJoin F C
  let X := Y ⊔ F.Li L 1
  let R := planeJoinResidual F C
  let E := conjugateSpanBy V R
  let Z := conjugateSpanBy (F.Vi 2) X
  have hYX : Y ≤ X := le_sup_left
  have hTY : (T : Subgroup G) ≤ Y := (planeCentralizerJoin_placements h F C).1
  have hTX : (T : Subgroup G) ≤ X := hTY.trans hYX
  have hLX : F.Li L 1 ≤ X := le_sup_right
  have hLV : F.Li L 1 ≤ normalizer (V : Set G) :=
    (F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes)
  obtain ⟨⟨eY⟩,_⟩ := four_plane_escape_binary_structure h earlier F hab C hfail (Or.inr rfl) hm
  have hjoin : Y ⊔ F.Li L 1 = X := rfl
  obtain ⟨eX⟩ := four_mixed_plane_escape_join_equiv h earlier F hab C hfail hm
  let q := eX.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := eX.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Finite (LinearGroup 4) := Finite.of_surjective q hq
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eX.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let YX := Y.subgroupOf X
  let Q := YX.map q
  let S := (T.subtype hTX).mapSurjective hq
  have hSY : (S : Subgroup _) ≤ Q := map_mono (comap_mono hTY)
  have hodd : Odd Q.index := by
    rw [← Nat.not_even_iff_odd,even_iff_two_dvd]
    exact fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le hSY))
  let f := q.subgroupMap YX
  have hkf : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.subgroupMap YX).ker
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let c := subgroupOfEquivOfLe hYX
  let eQ := (f.pCoreQuotientEquiv (q.subgroupMap_surjective YX) hkf).symm.trans
    ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (eY.trans (projectiveEquivLinear (by decide : 0 < 3)).symm))
  have ht := (FifteenPointSubgroups.psl4_coset_action
    (projectiveEquivLinear (by decide : 0 < 4)).symm Q hodd ⟨eQ⟩).1
  have hkerY : q.ker ≤ YX := (hk.le_sylow_of_normal (T.subtype hTX)).trans
    (comap_mono hTY)
  have hRT : R ⊔ (T : Subgroup G) = Y := by
    have hh := congrArg (map Y.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTY))
    rw [Subgroup.map_sup] at hh
    change R ⊔ ((T : Subgroup G).subgroupOf Y).map Y.subtype = (⊤ : Subgroup Y).map Y.subtype at hh
    simpa only [map_subgroupOf_eq_of_le hTY,←MonoidHom.range_eq_map,range_subtype] using hh
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := by
    simpa only [Gi,F.last] using F.invariant 4
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := hTY.trans
    (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pResidual 2 Y)))
  have hYE : Y ≤ normalizer (E : Set G) := by
    rw [←hRT]
    exact sup_le (le_normalizer_conjugateSpanBy V R) (normalizes_conjugateSpanBy V R _ hTV hTR)
  have hYA : Y ≤ normalizer (F.Vi 2 : Set G) := (planeCentralizerJoin_placements h F C).2
  have hVZ : V ≤ Z := by
    let W := conjugateSpanBy (F.Vi 2) (F.Li L 1)
    have hpW : F.Vi 1 ≤ W := (F.monotone (by decide)).trans (le_conjugateSpanBy _ _)
    have hWV : W ≤ V := conjugateSpanBy_le (F.le_seed 2) hLV
    rcases F.localKernel_irreducible L (by decide) h.chosen.normalizes
      (fun _ => ⟨h.naturalMarking⟩) W hpW hWV (le_normalizer_conjugateSpanBy _ _) with he | he
    · have hc := card_le_of_le ((le_conjugateSpanBy (F.Vi 2) (F.Li L 1)).trans he.le)
      rw [F.card 2 (by decide),F.card 1 (by decide)] at hc
      norm_num at hc
    · exact he.ge.trans (conjugateSpanBy_mono le_rfl hLX)
  have hUZ : F.UH X ≤ Z := conjugateSpanBy_le hVZ (le_normalizer_conjugateSpanBy _ _)
  have hLnot : ¬ F.Li L 1 ≤ Y := by
    intro hle
    have hnorm := hle.trans hYA
    rcases F.localKernel_irreducible L (by decide : 2 ≤ 4) h.chosen.normalizes
      (fun _ => ⟨h.naturalMarking⟩) (F.Vi 2) (F.monotone (by decide)) (F.le_seed 2) hnorm with he | he
    · have hh := congrArg (fun A : Subgroup G => Nat.card A) he
      rw [F.card 2 (by decide),F.card 1 (by decide)] at hh
      norm_num at hh
    · have hh := congrArg (fun A : Subgroup G => Nat.card A) (he.trans F.last.symm)
      rw [F.card 2 (by decide),F.card 4 (by decide)] at hh
      norm_num at hh
  obtain ⟨a,haL,haY⟩ := Set.not_subset.mp hLnot
  have hZE : Z ≤ E := by
    apply (closure_le _).mpr
    rintro _ ⟨g,hg,z,hz,rfl⟩
    by_cases hgY : g ∈ Y
    · exact le_conjugateSpanBy V R (F.le_seed 2
        ((mem_normalizer_iff.mp (hYA hgY) z).mp hz))
    obtain ⟨x,hx,y,hy,he⟩ := two_pretransitive_factorization_of_map q YX hkerY ht
      (a := (⟨a,hLX haL⟩ : X)) (b := (⟨g,hg⟩ : X)) haY hgY
    have hyA := (mem_normalizer_iff.mp (hYA hy) z).mp hz
    have haV := (mem_normalizer_iff.mp (hLV haL) ((y : G)*z*(y : G)⁻¹)).mp (F.le_seed 2 hyA)
    have hxE := (mem_normalizer_iff.mp (hYE hx) (a*((y : G)*z*(y : G)⁻¹)*a⁻¹)).mp
      (le_conjugateSpanBy V R haV)
    have heG : (x : G)*a*(y : G) = g := congrArg Subtype.val he
    rw [←heG]
    change ((x : G)*a*(y : G))*z*((x : G)*a*(y : G))⁻¹ ∈ E
    change (x : G) * (a * ((y : G) * z * (y : G)⁻¹) * a⁻¹) * (x : G)⁻¹ ∈ E at hxE
    simpa only [mul_inv_rev,mul_assoc] using hxE
  apply plane_escape_span_ne_residual_span h (Or.inl rfl) earlier F hab C hfail
  change E = F.UH (Y ⊔ F.Li L 1)
  rw [hjoin]
  exact le_antisymm (conjugateSpanBy_mono le_rfl ((map_subtype_le _).trans hYX)) (hUZ.trans hZE)


/-- All local-control clauses on the same flag in the mixed binary row. -/
theorem four_localControl_of_binary_five
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) : LocalControl C :=
  localControl_of_centralizers_and_models h (Or.inl rfl) earlier F C
    (point_quotient_centralizer_le_normalizer h (Or.inl rfl) earlier F hab C)
    (Or.inr (Or.inr hm)) (four_plane_bound_of_binary_five h earlier F hab C hm)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
