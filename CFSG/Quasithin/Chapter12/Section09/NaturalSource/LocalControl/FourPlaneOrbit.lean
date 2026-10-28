module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourPlaneLattice
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneResidual
public import Theory.GroupAction.TwoTransitiveFactorization
public import Theory.SpecificGroups.FifteenPointSubgroups.Actions

/-!
# The degree-four plane bound in the PSL₄(2) point row

The escaping plane join Y is an endpoint parabolic in K₁T, so its
left-coset action is two-transitive. Write R=O²(Y) and E=⟨V^R⟩.
The original Sylow normalizes V and R, hence Y=RT preserves E.
Choose a in L₁ outside Y. Two-transitivity writes every g outside Y
as xay with x,y in Y. Since Y preserves V₂ and a preserves V,
every X-conjugate of V₂ lies in E, where X=K₁T.
Irreducibility of the original L₁ action on V/V₁ shows that these
conjugates generate U_X. This contradicts the previously proved
I₂-normalization obstruction on the same flag.

Thus the plane-centralizer bound and the unchanged LocalControl record
hold in this point-model row. The A₇ and mixed PSL₅(2) rows in original
degree four remain separate obligations, as does the nonabelian catalogue.

Source: Aschbacher--Smith, 12.9.7, refs/quasithin.pdf, printed p.862.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The source plane bound for the original PSL₄(2) point-component quotient. -/
theorem four_plane_bound_of_binary_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2) :
    centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) := by
  classical
  by_contra hfail
  let := h.chosen.elementary
  let X := C.K1 ⊔ (T : Subgroup G)
  let Y := planeCentralizerJoin F C
  let R := planeJoinResidual F C
  let E := conjugateSpanBy V R
  let Z := conjugateSpanBy (F.Vi 2) X
  have hYX : Y ≤ X := inf_le_left
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTY : (T : Subgroup G) ≤ Y := (planeCentralizerJoin_placements h F C).1
  have hLX : F.Li L 1 ≤ X := C.contains.trans le_sup_left
  have hLV : F.Li L 1 ≤ normalizer (V : Set G) :=
    (F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes)
  obtain ⟨⟨eY⟩,hgen⟩ := four_plane_escape_binary_structure h earlier F hab C hfail (Or.inl rfl) hm
  have hjoin : Y ⊔ F.Li L 1 = X := hgen rfl
  obtain ⟨eX⟩ := four_point_join_binary_equiv h earlier F C (Or.inl rfl) hm
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
    have he : Y = X := (sup_eq_left.mpr hle).symm.trans hjoin
    exact (planeCentralizerJoin_lt_point_join h (Or.inl rfl) earlier F hab C).ne he
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

/-- Apply the proved plane bound to all original local-control clauses. -/
theorem four_localControl_of_binary_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2) : LocalControl C :=
  localControl_of_centralizers_and_models h (Or.inl rfl) earlier F C
    (point_quotient_centralizer_le_normalizer h (Or.inl rfl) earlier F hab C)
    (Or.inr (Or.inl hm)) (four_plane_bound_of_binary_four h earlier F hab C hm)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
