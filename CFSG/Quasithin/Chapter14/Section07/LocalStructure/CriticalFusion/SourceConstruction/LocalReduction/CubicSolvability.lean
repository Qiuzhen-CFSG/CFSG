module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicFaithfulCompletion
public import Theory.GroupAction.RankTwoCosetGeometry.CommutingSeeds
public import Theory.GroupTheory.ConjugatePairInternalLift
/-!
# Solvability of the original escaping cubic completion

Suppose the original cubic Y escapes N_G(L) in the normal-point branch.
A component of D = ⟨P,YT⟩ would give the natural rank-three seed W,
with C_D(W) = O₂(D) and the same abelian point-normalizer span U as V.
Normalizer transitivity and this common span show that intersecting
conjugates commute for the mixed family consisting of both V and W.

Apply the commuting-seed path argument to the literal LT–D coset geometry.
The two local seed centralizers are their two-cores and lie in the common
Sylow T. Thus every conjugate of V under ⟨LT,D⟩ lies in LT and centralizes V.
Its normal span is a nontrivial two-subgroup of O₂(LT), normalized by both
vertices. Uniqueness of the maximal two-local over LT puts its normalizer
in N_G(L), contradicting the original escape of Y. This excludes components
and hence proves D solvable, with no local classification callback.

The final application supplies Y, its exact star kernel and S₃ quotient
from the actual order-four chief interval. The remaining solvable analysis
of 14.5.3(2), small-interval exclusions and 14.7.52 assembly remain open.
EarlierFaithfulClassification retains its existing 14.3.4 producer.

Source: Aschbacher–Smith, 14.5.8, printed pp.1014–1015, and its use
in 14.7.20(2), p.1049, refs/quasithin.pdf. The path induction is the
source's symmetric critical-pair contradiction without choosing its radius.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- Intersecting conjugates commute even when the two seeds have different types. -/
theorem cubic_generated_component_seed_family_commutes_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let S : Bool → Subgroup G := fun i => if i then W else V
    ∀ i j g k, (S i).conjBy g ⊓ (S j).conjBy k ≠ ⊥ →
      ⁅(S i).conjBy g,(S j).conjBy k⁆ = ⊥ := by
  let := hab
  let := h.chosen.elementary
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let S : Bool → Subgroup G := fun i => if i then W else V
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨e,f,_,_,hf⟩ := cubic_generated_component_natural_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨_,_,hWU,hspan,_,_⟩ := cubic_generated_component_span_geometry_of_normalizes_point
    h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨z,hz1,hZ⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzW : z ∈ W := le_conjugateSpanBy _ _ (hZ ▸ mem_zpowers z)
  have hzV : z ∈ V := F.le_seed 1 (hZ ▸ mem_zpowers z)
  have htrans : ∀ i, ∀ x ∈ S i, x ≠ 1 →
      ∃ n ∈ normalizer (S i : Set G), (MulAut.conj n) z = x := by
    intro i x hx hx1
    cases i with
    | false =>
      obtain ⟨l,hl,he⟩ := h.vector_transitive hzV hx hz1 hx1
      exact ⟨l,h.chosen.normalizes hl,he⟩
    | true =>
      let zW : W := ⟨z,hzW⟩
      let xW : W := ⟨x,hx⟩
      have hzn : (f zW).toAdd ≠ 0 := by
        intro hh
        have hfz : f zW = 1 := hh
        exact hz1 (congrArg Subtype.val (f.injective (hfz.trans f.map_one.symm)))
      have hxn : (f xW).toAdd ≠ 0 := by
        intro hh
        have hfx : f xW = 1 := hh
        exact hx1 (congrArg Subtype.val (f.injective (hfx.trans f.map_one.symm)))
      obtain ⟨a,ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hzn hxn
      obtain ⟨g,hg⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective C)) a
      refine ⟨g,(le_normalizer_conjugateSpanBy _ _) g.property,?_⟩
      have hh := hf g zW
      change e (q g) = a at hg
      change (f (W.normalizerMonoidHom
        (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW)).toAdd =
          BinaryLinearThree.W (e (q g)) (f zW).toAdd at hh
      rw [hg] at hh
      have hfx : f (W.normalizerMonoidHom
          (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW) = f xW :=
        Multiplicative.toAdd.injective (hh.trans ha)
      exact congrArg Subtype.val (f.injective hfx)
  have hle : ∀ i, S i ≤ F.U := by
    intro i
    cases i
    · exact le_conjugateSpanBy _ _
    · exact hWU
  have hsp : ∀ i, conjugateSpanBy (S i) (centralizer ({z} : Set G)) ≤ F.U := by
    intro i
    rw [←F.H_eq_centralizer (by decide) z hZ]
    cases i
    · exact le_rfl
    · exact hspan.le
  change ∀ (i j : Bool) (g k : G), (S i).conjBy g ⊓ (S j).conjBy k ≠ ⊥ →
    ⁅(S i).conjBy g,(S j).conjBy k⁆ = ⊥
  intro i j g k hi
  exact mixed_conjugates_commute (S i) (S j)
    (mixed_intersection_commutes (S i) (S j) F.U hz1 (hle i) (hsp j) (htrans i) (htrans j))
    g k hi

/-- The original full point-normality interface. -/
theorem cubic_generated_component_seed_family_commutes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let S : Bool → Subgroup G := fun i => if i then W else V
    ∀ i j g k, (S i).conjBy g ⊓ (S j).conjBy k ≠ ⊥ →
      ⁅(S i).conjBy g,(S j).conjBy k⁆ = ⊥ := by
  apply cubic_generated_component_seed_family_commutes_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The ambient uniqueness argument excludes every component of D. -/
theorem cubic_generated_no_component_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) : False := by
  let A := L ⊔ (T : Subgroup G)
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let E := A ⊔ D
  let S : Bool → Subgroup G := fun i => if i then W else V
  let M : Bool → Subgroup G := fun i => if i then D else A
  let M₀ := ChapterF.Section07.Geometry.family A D
  let S₀ : Bool → Subgroup E := fun i => (S i).subgroupOf E
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hVD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hSE : ∀ i, S i ≤ E := by
    intro i
    cases i
    · exact h.chosen.le_sylow.trans (le_sup_right.trans le_sup_left)
    · exact (conjugateSpanBy_le_self hVD).trans le_sup_right
  have hSM : ∀ i, S i ≤ M i := by
    intro i
    cases i
    · exact h.chosen.le_sylow.trans le_sup_right
    · exact conjugateSpanBy_le_self hVD
  have hnM : ∀ i, M i ≤ normalizer (S i : Set G) := by
    intro i
    cases i
    · exact sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural)
    · exact le_normalizer_conjugateSpanBy _ _
  have hQTA : A.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow A (T.subtype (show (T : Subgroup G) ≤ A from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ A from le_sup_right)] using hh
  have hQTD : D.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow D (T.subtype hTD)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD] using hh
  have hk := cubic_generated_component_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  have hlocalC : ∀ i j, i ≠ j → M i ⊓ centralizer (S i : Set G) ≤ M j := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact (h.centralizer_LT structural).le.trans (hQTA.trans hTD)
    · intro x hx
      have hxC : (⟨x,hx.1⟩ : D) ∈ centralizer (W.subgroupOf D : Set D) := by
        intro w hw
        apply Subtype.ext
        exact mem_centralizer_iff.mp hx.2 w hw
      have hxQ : (⟨x,hx.1⟩ : D) ∈ pCore 2 D := hk ▸ hxC
      exact (le_sup_right : (T : Subgroup G) ≤ A) (hQTD (mem_map_of_mem D.subtype hxQ))
    · exact (hij rfl).elim
  have hmap (i : Bool) (g : E) :
      ((S₀ i).conjBy g).map E.subtype = (S i).conjBy (g : G) := by
    rw [map_conjBy_hom,map_subgroupOf_eq_of_le (hSE i)]
    rfl
  have hgen := ChapterF.Section07.Geometry.family_generates A D
  have hle₀ : ∀ i, S₀ i ≤ M₀ i := by
    intro i x hx
    have hh : (x : G) ∈ M i := hSM i hx
    cases i <;> exact hh
  have hn₀ : ∀ i, M₀ i ≤ normalizer (S₀ i : Set E) := by
    intro i
    have hh := (comap_mono (f := E.subtype) (hnM i)).trans (le_normalizer_comap E.subtype)
    cases i <;> exact hh
  have hC₀ : ∀ i j, i ≠ j → M₀ i ⊓ centralizer (S₀ i : Set E) ≤ M₀ j := by
    intro i j hij x hx
    have hxM : (x : G) ∈ M i := by cases i <;> exact hx.1
    have hxC : (x : G) ∈ centralizer (S i : Set G) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx.2 (⟨y,hSE i hy⟩ : E) hy)
    have hh := hlocalC i j hij ⟨hxM,hxC⟩
    cases j <;> exact hh
  have hc := cubic_generated_component_seed_family_commutes_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  have hc₀ : ∀ i j (g k : E), (S₀ i).conjBy g ⊓ (S₀ j).conjBy k ≠ ⊥ →
      ⁅(S₀ i).conjBy g,(S₀ j).conjBy k⁆ = ⊥ := by
    intro i j g k hi
    have hi' : (S i).conjBy (g : G) ⊓ (S j).conjBy (k : G) ≠ ⊥ := by
      rw [←hmap i g,←hmap j k,←map_inf _ _ _ E.subtype_injective]
      exact fun hz => hi ((map_eq_bot_iff_of_injective _ E.subtype_injective).mp hz)
    apply (map_eq_bot_iff_of_injective _ E.subtype_injective).mp
    rw [map_commutator,hmap,hmap]
    exact hc i j g k hi'
  obtain ⟨hfix,hcomm⟩ := CosetGeometry.RankTwo.conjugate_seeds_in_overlap M₀ S₀ hgen hle₀ hn₀ hC₀ hc₀
  let N := conjugateSpanBy V E
  have hNA : N ≤ A := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,v,hv,rfl⟩
    have hh := hfix false (⟨g,hg⟩ : E)
    have hm := map_mono (f := E.subtype) (hh.trans inf_le_left)
    rw [hmap] at hm
    have hMA : (M₀ false).map E.subtype = A := map_subgroupOf_eq_of_le le_sup_left
    rw [hMA] at hm
    exact hm (mem_map_of_mem _ hv)
  have hNC : N ≤ centralizer (V : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,v,hv,rfl⟩
    have hh := congrArg (map E.subtype) (hcomm false false 1 (⟨g,hg⟩ : E))
    rw [map_commutator,hmap,hmap,Subgroup.map_bot] at hh
    change ⁅V.conjBy 1,V.conjBy g⁆ = ⊥ at hh
    rw [conjBy_one] at hh
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
      (mem_map_of_mem _ hv)
  have hNQ : N ≤ A.pCoreIn 2 := (le_inf hNA hNC).trans (h.centralizer_LT structural).le
  have hNp : IsPGroup 2 N := (isPGroup_pCoreIn 2 A).to_le hNQ
  have hNne : N ≠ ⊥ := fun hz => h.chosen.ne_bot (eq_bot_iff.mpr
    ((le_conjugateSpanBy V E).trans hz.le))
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have hcontrol : normalizer (N : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal
      (fun M hM hAM => Set.mem_singleton_iff.mp ((h.maximal_unique structural hu).2 ▸
        show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ A ≤ M} from ⟨hM,hAM⟩))
      hNp hNne (le_sup_left.trans (le_normalizer_conjugateSpanBy V E))
  exact hout (((le_sup_left.trans le_sup_right : Y ≤ D).trans le_sup_right).trans
    ((le_normalizer_conjugateSpanBy V E).trans hcontrol))

/-- The original full point-normality interface. -/
theorem cubic_generated_no_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) : False := by
  apply cubic_generated_no_component_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Source 14.5.8 in the normal-point branch used by the small-chief exclusion. -/
theorem cubic_generated_solvable_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G) := by
  classical
  by_contra hs
  obtain ⟨J,hJD,hJ,_⟩ := cubic_generated_nonsolvable_component_of_normalizes_point
    h hab structural previous faithful Y hYH hYL hYp hYT hout he hs
  exact cubic_generated_no_component_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he (J.subgroupOf _) hJ

/-- The original full point-normality interface. -/
theorem cubic_generated_solvable
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G) := by
  apply cubic_generated_solvable_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The original order-four interval yields a solvable cubic completion, retaining
the selected Y, its exact original star kernel and its S₃ overgroup quotient. -/
theorem extraspecial_four_interval_cubic_solvable
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G) := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,
    cubic_generated_solvable h hab structural previous faithful hn Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
