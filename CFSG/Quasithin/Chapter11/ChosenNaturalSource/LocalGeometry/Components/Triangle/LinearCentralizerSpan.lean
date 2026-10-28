module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearCubicMovement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.RadicalAction.Action
public import Theory.Representation.SL3.ParabolicSubgroups
public import Theory.Representation.SL3.PointLocalFixed
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import Theory.Frattini.PGroupMap


/-!
# The original linear centralizer span

The first parabolic acts irreducibly on V/V₁. To prove this on the actual
binary subgroup interval, use the original natural equivalence and common
Sylow alignment: a proper additive subgroup invariant under the point-local
SL₃ group is fixed and therefore lies on its defining line. No field-linearity
of the intermediate subgroup is assumed.

Apply G.2.2 with the perfect first residual as local actor and N_G(V₁) as
overgroup. The source span U = ⟨V^{C_G(V₁)}⟩ lies in this larger closure,
so U ≤ T, U ≤ O₂(C_G(V₁)), and Φ(U), [U,U] ≤ V₁. The original quotient
map also gives Û ≤ Z(O₂(C_G(V₁)/V₁)). Both KX and T normalize U, and U
is normal in the original T. These statements retain the same V, point,
Cartan, containing component and quotient maps.

The common-Q application discharges the U ≤ T premise of the cubic-core
dichotomy. Nonzero [C_U(X₁),X] from the extraspecial three-group action,
the subsequent centralizer and module branches, common-normal existence,
both triangle orientations and full 11.1.1--3 assembly remain with
qt-d-1222-natural-relative-components. Earlier-source inputs retain their
producers and final discharge by qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, proof of
11.1.2, printed p.763, the G.2.2 paragraph preceding the extraspecial action.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open SL3 SL3.PlaneAction SL3.RadicalAction
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

private theorem point_interval (A : Subgroup G)
    (hPA : (flag D S m).Vi 0 ≤ A) (hAV : A ≤ V)
    (hn : (flag D S m).Li 0 ≤ normalizer (A : Set G)) :
    A = (flag D S m).Vi 0 ∨ A = V := by
  classical
  by_cases he : A = V
  · exact .inr he
  left
  let e := vectorEquiv D S m
  let W := ((A.subgroupOf V).map e.toMonoidHom).toAddSubgroup
  have hproper : W ≠ ⊤ := by
    intro ht
    apply he
    apply le_antisymm hAV
    intro v hv
    have hw : (e ⟨v,hv⟩).toAdd ∈ W := ht.ge (AddSubgroup.mem_top _)
    obtain ⟨w,hw,hew⟩ := hw
    have hew' : (w : G) = v := congrArg Subtype.val (e.injective hew)
    simpa only [hew'] using (show (w : G) ∈ A from hw)
  have hi : ∀ g ∈ Matrix.PSL3.LinearThree.pointLocalSL S.field.Carrier,
      ∀ w ∈ W, g.val.mulVec w ∈ W := by
    intro g hg w hw
    obtain ⟨l,hl⟩ := localProjection_surjective D S m 0 ⟨g,hg⟩
    obtain ⟨v,hv,rfl⟩ := hw
    have hconj := alignedAction_projection D S m
      (inclusion le_sup_left (⟨l,(localResidual_le _ l.property).1⟩ : L)) v
    rw [alignedAction_component,←localProjection_coe,hl] at hconj
    refine ⟨V.normalizerMonoidHom
      (inclusion (ambientJoin_normalizes_seed D S)
        (inclusion le_sup_left (⟨l,(localResidual_le _ l.property).1⟩ : L))) v,?_,?_⟩
    · exact le_normalizer_iff.mp hn l l.property v hv
    · exact congrArg Multiplicative.ofAdd hconj
  apply le_antisymm ?_ hPA
  intro a ha
  have hw : (e ⟨a,hAV ha⟩).toAdd ∈ W := mem_map_of_mem e.toMonoidHom ha
  obtain ⟨c,hc⟩ := SL3ParabolicNatural.point_fixed_line _
    (fun g hg => SL3ParabolicNatural.point_invariant_fixed W hproper hi g hg _ hw)
  apply ((SL3.coordinates D S m).mem_preimage _ ⟨a,hAV ha⟩).mpr
  apply (mem_flagFor_iff (alignment D S m) 0 _).mpr
  change (e ⟨a,hAV ha⟩).toAdd ∈ SL3.Model.point
  rw [hc]
  simp


/-- The original first parabolic acts irreducibly on the literal V/V₁. -/
theorem linear_point_interval_irreducible
    (f : InvariantFlag (.sl3 m)) (A : Subgroup G)
    (hPA : f.Vi 0 ≤ A) (hAV : A ≤ V)
    (hn : f.Li 0 ≤ normalizer (A : Set G)) : A = f.Vi 0 ∨ A = V := by
  have hp : f.Vi 0 = (flag D S m).Vi 0 := congrArg (Coordinates.sl3 m).preimage
    (flag_unique D S m 0 (f.space 0) (f.dimension 0) (f.invariant 0))
  have hl : f.Li 0 = (flag D S m).Li 0 := congrArg (localResidual L) hp
  rw [hp] at hPA ⊢
  rw [hl] at hn
  exact point_interval D S m A hPA hAV hn

private theorem normalizer_hypothesis (f : InvariantFlag (.sl3 m)) :
    (ChapterG.Section02.Setup.mk V (f.Vi 0) (f.Li 0) T
      (normalizer (f.Vi 0 : Set G))).Hypothesis := by
  let B := ChapterG.Section02.Setup.mk V (f.Vi 0) (f.Li 0) T
    (normalizer (f.Vi 0 : Set G))
  have hLN : f.Li 0 ≤ normalizer (f.Vi 0 : Set G) :=
    (localResidual_le _).trans inf_le_right
  have hLV : f.Li 0 ≤ normalizer (V : Set G) :=
    ((localResidual_le _).trans inf_le_left).trans D.normalizes
  have hr : pResidual 2 (f.Li 0) = ⊤ := by
    let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
    apply (pResidual_eq_top_iff 2 (f.Li 0)).mpr
    intro N hN hq
    let := hN
    let : Group.IsNilpotent (f.Li 0 ⧸ N) := hq.isNilpotent
    have hh := solvableResidual_le_of_solvable_quotient N
    rwa [solvableResidual_eq_top,top_le_iff] at hh
  have hb : B.L₁ = f.Li 0 := by
    change (pResidual 2 (f.Li 0 ⊓ normalizer (f.Vi 0 : Set G) : Subgroup G)).map
      (f.Li 0 ⊓ normalizer (f.Vi 0 : Set G)).subtype = _
    rw [inf_eq_left.mpr hLN,hr,←MonoidHom.range_eq_map,range_subtype]
  have hne : f.Vi 0 ≠ V := by
    intro he
    have hs := (Coordinates.sl3 m).preimage_injective
      (he.trans (Coordinates.sl3 m).preimage_top.symm)
    have hd := f.dimension 0
    rw [hs,finrank_top] at hd
    change Module.finrank S.field.Carrier (Fin 3 → S.field.Carrier) = 1 at hd
    rw [Module.finrank_fin_fun] at hd
    norm_num at hd
  refine {
    elementary := D.elementary
    point_ne_bot := f.V_ne_bot 0
    point_le := D.centralQuotientPreimage_le _
    residual := hr
    V_le_T := D.le_sylow
    T_normalizes_point := f.invariant 0
    T_normalizes_V := S.sylow_normalizes
    T_normalizes_L := f.sylow_normalizes_Li 0
    sylow_LT := ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    H_le := le_rfl
    local_le := ?_
    sylow_H := ⟨T.subtype (f.invariant 0),map_subgroupOf_eq_of_le (f.invariant 0)⟩
    characteristic_two := (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (Chapter1.mem_He_iff.mp (f.normalizer_mem_He S 0))
    local_normalizes_V := ?_
    quotient_nonzero := hne
    irreducible := ?_ }
  · change B.L₁ ⊔ (T : Subgroup G) ≤ normalizer (f.Vi 0 : Set G)
    rw [hb]
    exact sup_le hLN (f.invariant 0)
  · change B.L₁ ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
    rw [hb]
    exact sup_le hLV S.sylow_normalizes
  · intro A hPA hAV hn
    change B.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) at hn
    rw [hb] at hn
    exact linear_point_interval_irreducible D S m f A hPA hAV (le_sup_left.trans hn)

/-- G.2.2 in the actual point normalizer, proved from the original flag. -/
theorem linear_point_normalizer_span
    (f : InvariantFlag (.sl3 m)) :
    let N := normalizer (f.Vi 0 : Set G)
    let W := conjugateSpanBy V N
    W ≤ N.pCoreIn 2 ∧ W ≤ (T : Subgroup G) ∧
      (frattini W).map W.subtype ≤ f.Vi 0 ∧ ⁅W,N.pCoreIn 2⁆ ≤ f.Vi 0 := by
  have h := normalizer_hypothesis D S m f
  exact ⟨h.U_le_core,h.U_normal_in_T.1,h.frattini_U_le_point,h.commutator_U_core_le_point⟩

/-- The literal centralizer span used in 11.1.2 lies in T and in the
centralizer's own two-core; its Frattini and derived subgroups lie in V₁. -/
theorem linear_point_centralizer_span
    (f : InvariantFlag (.sl3 m)) :
    let C := centralizer (f.Vi 0 : Set G)
    let U := conjugateSpanBy V C
    U ≤ C.pCoreIn 2 ∧ U ≤ (T : Subgroup G) ∧
      (frattini U).map U.subtype ≤ f.Vi 0 ∧ ⁅U,U⁆ ≤ f.Vi 0 ∧
      ⁅U,(normalizer (f.Vi 0 : Set G)).pCoreIn 2⁆ ≤ f.Vi 0 := by
  let C := centralizer (f.Vi 0 : Set G)
  let N := normalizer (f.Vi 0 : Set G)
  let U := conjugateSpanBy V C
  let W := conjugateSpanBy V N
  obtain ⟨hWN,hWT,hΦ,hcomm⟩ := linear_point_normalizer_span D S m f
  have hUW : U ≤ W := conjugateSpanBy_mono le_rfl (Subgroup.centralizer_le_normalizer _)
  have hUT : U ≤ (T : Subgroup G) := hUW.trans hWT
  have hp : IsPGroup 2 U := T.isPGroup'.to_le hUT
  have hUC : U ≤ C := by
    let := D.elementary
    apply conjugateSpanBy_le_self
    exact V.le_centralizer.trans (centralizer_le (D.centralQuotientPreimage_le _))
  have hcore : U ≤ C.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp hUC (le_normalizer_conjugateSpanBy _ _)
  have hΦU : (frattini U).map U.subtype ≤ (frattini W).map W.subtype := by
    let : Fact (IsPGroup 2 U) := ⟨hp⟩
    let : Fact (IsPGroup 2 W) := ⟨T.isPGroup'.to_le hWT⟩
    have hh := map_mono (f := W.subtype)
      (frattini_map_le_of_isPGroup (p := 2) (inclusion hUW))
    simpa only [map_map,subtype_comp_inclusion] using hh
  exact ⟨hcore,hUT,hΦU.trans hΦ,
    (commutator_mono hUW (hUW.trans hWN)).trans hcomm,
    (commutator_mono hUW le_rfl).trans hcomm⟩

/-- The source's literal quotient formulation: the image of the original
centralizer span lies in the center of O₂(C_G(V₁)/V₁). -/
theorem linear_point_centralizer_span_quotient
    (f : InvariantFlag (.sl3 m)) :
    let C := centralizer (f.Vi 0 : Set G)
    let P := (f.Vi 0).subgroupOf C
    let : P.Normal := normal_subgroupOf_of_le_normalizer (Subgroup.centralizer_le_normalizer _)
    let U := conjugateSpanBy V C
    (U.subgroupOf C).map (QuotientGroup.mk' P) ≤
      (center (pCore 2 (C ⧸ P))).map (pCore 2 (C ⧸ P)).subtype := by
  let C := centralizer (f.Vi 0 : Set G)
  let P := (f.Vi 0).subgroupOf C
  let : P.Normal := normal_subgroupOf_of_le_normalizer (Subgroup.centralizer_le_normalizer _)
  let U := conjugateSpanBy V C
  let π := QuotientGroup.mk' P
  change (U.subgroupOf C).map π ≤
    (center (pCore 2 (C ⧸ P))).map (pCore 2 (C ⧸ P)).subtype
  have hk : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact (@IsElementaryAbelian.isPGroup 2 _ _
      (D.centralQuotientPreimage_elementary _)).comap_subtype
  have hpre : (pCore 2 (C ⧸ P)).comap π = pCore 2 C :=
    π.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk
  have hmap : (pCore 2 C).map π = pCore 2 (C ⧸ P) := by
    rw [←hpre,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  obtain ⟨hcore,_,_,_,hcomm⟩ := linear_point_centralizer_span D S m f
  have hCN : C.pCoreIn 2 ≤ (normalizer (f.Vi 0 : Set G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (Subgroup.centralizer_le_normalizer _)
      (normalizer_le_normalizer_centralizer (f.Vi 0))
  rintro z ⟨u,hu,rfl⟩
  have huC : u ∈ pCore 2 C := by
    obtain ⟨v,hv,he⟩ := hcore hu
    exact C.subtype_injective he ▸ hv
  have huq : π u ∈ pCore 2 (C ⧸ P) := hmap.le (mem_map_of_mem π huC)
  refine ⟨⟨π u,huq⟩,mem_center_iff.mpr ?_,rfl⟩
  intro y
  obtain ⟨q,hq⟩ := QuotientGroup.mk'_surjective P (y : C ⧸ P)
  have hqC : q ∈ pCore 2 C := hpre.le (by
    change π q ∈ pCore 2 (C ⧸ P)
    rw [hq]
    exact y.property)
  have hcomm' : ⁅u,q⁆ ∈ P :=
    hcomm (commutator_mem_commutator hu (hCN (mem_map_of_mem C.subtype hqC)))
  have he : π ⁅u,q⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm'
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at he
  apply Subtype.ext
  change (y : C ⧸ P) * π u = π u * (y : C ⧸ P)
  rw [←hq]
  exact he.symm


omit [Finite G] in
private theorem normalizes_span_of_normalizes_both
    {A B : Subgroup G} (hAV : A ≤ normalizer (V : Set G))
    (hAB : A ≤ normalizer (B : Set G)) : A ≤ normalizer (conjugateSpanBy V B : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro a ha x ⟨b,hb,v,hv,rfl⟩
  refine subset_closure ⟨a*b*a⁻¹,le_normalizer_iff.mp hAB a ha b hb,
    a*v*a⁻¹,le_normalizer_iff.mp hAV a ha v hv,?_⟩
  group

/-- The original KX and T act on the same source span, and its normality
in T follows from the proved G.2.2 containment. -/
theorem linear_point_centralizer_span_actors
    (f : InvariantFlag (.sl3 m))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K) :
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    (K ⊔ X) ⊔ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      (U.subgroupOf (T : Subgroup G)).Normal := by
  intro U
  have hp : f.Vi 0 = (flag D S m).Vi 0 := congrArg (Coordinates.sl3 m).preimage
    (flag_unique D S m 0 (f.space 0) (f.dimension 0) (f.invariant 0))
  have hXN : X ≤ normalizer (f.Vi 0 : Set G) := by
    rw [hp]
    exact SL3.cartan_normalizes D S m hX 0
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨SL3.flagLocalCoreEquiv S m f 0⟩⟩
  have hKC := subspace_containing_component_centralizes D S f (f.Vi 0)
    le_rfl hm hfix hK hLK
  have hKU : K ≤ normalizer (U : Set G) :=
    hKC.trans (le_normalizer_conjugateSpanBy _ _)
  have hXU : X ≤ normalizer (U : Set G) :=
    normalizes_span_of_normalizes_both ((hX.1.trans inf_le_left).trans D.normalizes)
      (hXN.trans (normalizer_le_normalizer_centralizer (f.Vi 0)))
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    normalizes_span_of_normalizes_both S.sylow_normalizes
      ((f.invariant 0).trans (normalizer_le_normalizer_centralizer (f.Vi 0)))
  exact ⟨sup_le (sup_le hKU hXU) hTU,
    (normal_subgroupOf_iff_le_normalizer (linear_point_centralizer_span D S m f).2.1).mpr hTU⟩

/-- The common-Q consumer with the G.2.2 span premise discharged. Nonzero
cubic displacement is still the extraspecial-action obligation of this owner. -/
theorem linear_triangle_centralizer_span_of_common_normal
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hgen : f.Li 0 ⊔ K₀ = K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual L E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    ⁅U ⊓ centralizer (E : Set G),X⁆ ≠ ⊥ →
    (let C := centralizer (f.Vi 0 : Set G)
     let P := (f.Vi 0).subgroupOf C
     let : P.Normal := normal_subgroupOf_of_le_normalizer (Subgroup.centralizer_le_normalizer _)
     (U.subgroupOf C).map (QuotientGroup.mk' P) ≤
       (center (pCore 2 (C ⧸ P))).map (pCore 2 (C ⧸ P)).subtype) ∧
    U ≤ (centralizer (f.Vi 0 : Set G)).pCoreIn 2 ∧
    U ≤ (T : Subgroup G) ∧ (frattini U).map U.subtype ≤ f.Vi 0 ∧
    ⁅U,U⁆ ≤ f.Vi 0 ∧ (K ⊔ X) ⊔ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
    (U.subgroupOf (T : Subgroup G)).Normal ∧ E ≤ H ∧ X ≤ H ∧ H ≤ centralizer (E : Set G) ∧
    Source.IsSL (H ⧸ pCore 2 H) 3 4 ∧
    H.pCoreIn 2 = H ⊓ L.pCoreIn 2 ∧ H ⊔ L.pCoreIn 2 = L ∧
    V = ⁅V,H⁆ ∧ ¬ normalizer (E : Set G) ≤ normalizer (L : Set G) ∧
    (⁅H.pCoreIn 2,H⁆ ≠ ⊥ ∨
      (¬ ⁅U ⊓ centralizer (E : Set G),X⁆ ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ¬ U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  intro E H U hY
  obtain ⟨hcore,hUT,hΦ,hderived,_⟩ := linear_point_centralizer_span D S m f
  obtain ⟨hactors,hnormal⟩ := linear_point_centralizer_span_actors D S m f hfix hX hK.1 hLK.le
  exact ⟨linear_point_centralizer_span_quotient D S m f,hcore,hUT,hΦ,hderived,hactors,hnormal,
    linear_triangle_cubic_core_dichotomy_of_common_normal D S m f hd hfix hX hK hLK
      hK₀ hK₀K hTK₀ hgen hk hp hcard hmove hQ hQT hTQ hKQ hLQ hUT hY⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
