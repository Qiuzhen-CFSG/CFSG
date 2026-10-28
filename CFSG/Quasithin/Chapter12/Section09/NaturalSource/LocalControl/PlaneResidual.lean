module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneReduction
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianParabolics
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.BinaryConjugationSection.ConjugationCoordinates
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The original two-residual and the plane-module obstruction

Let Y be the literal point/plane intersection of PlaneReduction and put
R = O²(Y). Since Y is its plane centralizer times the original Sylow,
R fixes V₂. Relative normality of I₂ in G₂ puts [I₂,R] in O₂(I₂),
which lies in Y. Removing this normalizing two-group supplement proves
that the original I₂ normalizes R, without a model hypothesis on Y.

The original I₂ and L₁T generate LT in both degrees. If the plane bound
fails, H = Y join L₁ escapes M. Its local span U_H therefore cannot equal
E = ⟨V^R⟩: that equality would make LT normalize the nontrivial two-group
U_H, and maximal-local uniqueness would force H into M. Thus V₂ < E < U_H.
In coordinates on the actual U_H/V₂, E supplies a proper nonzero
R-invariant subspace. The final theorem constructs this quotient action
with its literal projection, rather than assuming a representation marking.

The source overgroup lattice and four-space recognition must still force
irreducibility of this same action. This module does not assert the plane
bound or LocalControlInput.

Source: Aschbacher--Smith, 12.9.7, printed p.862 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The literal ambient image of O²(Y), with Y on the original flag. -/
@[expose] def planeJoinResidual (F : InvariantFlag T V n)
    (C : ComponentGeometry F L) : Subgroup G :=
  (pResidual 2 (planeCentralizerJoin F C)).map (planeCentralizerJoin F C).subtype

/-- The literal O²(Y) fixes V₂ since Y is its plane centralizer times T. -/
theorem planeJoinResidual_centralizes_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    planeJoinResidual F C ≤ centralizer (F.Vi 2 : Set G) := by
  let D := (C.K1 ⊔ (T : Subgroup G)) ⊓ centralizer (F.Vi 2 : Set G)
  have ht : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    (le_inf (le_sup_right.trans (C.K1 ⊔ (T : Subgroup G)).le_normalizer)
      ((F.invariant 2).trans (normalizer_le_normalizer_centralizer (F.Vi 2)))).trans
        inf_normalizer_le_normalizer_inf
  have he : planeJoinResidual F C = (pResidual 2 D).map D.subtype := by
    rw [planeJoinResidual,planeCentralizerJoin_eq_centralizer_sup_sylow h F C,
      ←embedded_pResidual_sup_sylow_of_normalizes T D ht]
    exact embedded_pResidual_join_pGroup _ _ (isPPerfect_embedded_pResidual 2 D)
      T.isPGroup' (ht.trans (normalizer_le_normalizer_characteristic_image D (pResidual 2 D)))
  rw [he]
  exact (map_subtype_le _).trans inf_le_right

/-- The original I₂ normalizes O²(Y), using the actual plane-action kernel. -/
theorem planeCoreClosure_normalizes_planeJoinResidual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    planeCoreClosure F ≤ normalizer (planeJoinResidual F C : Set G) := by
  let := h.chosen.elementary
  let Y := planeCentralizerJoin F C
  let R := planeJoinResidual F C
  let I := planeCoreClosure F
  let Q := I.pCoreIn 2
  have hRY : R ≤ Y := map_subtype_le _
  have hTY : (T : Subgroup G) ≤ Y := (planeCentralizerJoin_placements h F C).1
  have hYG : Y ≤ F.Gi 2 := (planeCentralizerJoin_placements h F C).2
  have hIG : I ≤ F.Gi 2 := (planeCoreClosure_le_parabolic h F).trans
    (F.P_le_G₂ (by have := h.rank; omega) L h.chosen.normalizes)
  have hGI : F.Gi 2 ≤ normalizer (I : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hIG).mp (planeCoreClosure_normal h F)
  have hGQ : F.Gi 2 ≤ normalizer (Q : Set G) := hGI.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hQY : Q ≤ Y := by
    have hQG : Q ≤ (F.Gi 2).pCoreIn 2 := pCoreIn_mono_of_normalizes hIG hGI
    have hQT := pCoreIn_le_sylow (F.Gi 2) (T.subtype (F.invariant 2))
    change (F.Gi 2).pCoreIn 2 ≤
      ((T : Subgroup G).subgroupOf (F.Gi 2)).map (F.Gi 2).subtype at hQT
    rw [map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ F.Gi 2 from F.invariant 2)] at hQT
    exact hQG.trans (hQT.trans hTY)
  have hRC : R ≤ centralizer (F.Vi 2 : Set G) :=
    planeJoinResidual_centralizes_plane h F C
  have hm := point_core_moves_plane_of_controlled_models h hn earlier F C
    (point_quotient_centralizer_le_normalizer h hn earlier F hab C)
    (point_models_of_abelian h hn earlier F hab C)
  have hQ := (planeCoreClosure_quotient h earlier F
    (point_core_moves_plane_of_component C hm)).1
  have hc : ⁅I,R⁆ ≤ Q := by
    change ⁅I,R⁆ ≤ (planeCoreClosure F).pCoreIn 2
    rw [hQ]
    apply le_inf
    · exact le_normalizer_iff_commutator_le_left.mp ((hRY.trans hYG).trans hGI)
    · exact (commutator_mono le_rfl hRC).trans
        (le_normalizer_iff_commutator_le_right.mp
          (hIG.trans (normalizer_le_normalizer_centralizer (F.Vi 2))))
  exact normalizes_residual_of_commutator_le_two I Y Y Q Y.le_normalizer hQY
    (isPGroup_pCoreIn 2 I) (hIG.trans hGQ) hc

/-- The original omitted-point parabolic and point parabolic generate LT. -/
theorem point_parabolics_generate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) :
    F.P L ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = L ⊔ (T : Subgroup G) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by have := h.rank; omega)
  let := h.chosen.elementary
  apply le_antisymm
  · exact sup_le inf_le_left (sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl)
  · rw [← F.orderedParabolic_generation_of_full_binary_action (by have := h.rank; omega) L
      h.chosen.normalizes h.full_L_action]
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    by_cases he : j = 1
    · subst j
      rw [F.orderedParabolic_one]
      exact le_sup_left
    · have hPH : F.orderedParabolic L j ≤ F.H :=
        F.orderedParabolic_le_H (by have := h.rank; omega) L (by omega)
      exact (le_inf inf_le_left hPH).trans
        ((Components.point_residual_sylow_eq_intersection h earlier F).ge.trans le_sup_right)

/-- The original I₂ together with L₁ and T generates LT in both degrees. -/
theorem planeCoreClosure_point_generate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    planeCoreClosure F ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = L ⊔ (T : Subgroup G) := by
  have hm := point_core_moves_plane_of_controlled_models h hn earlier F C
    (point_quotient_centralizer_le_normalizer h hn earlier F hab C)
    (point_models_of_abelian h hn earlier F hab C)
  have hp := planeCoreClosure_sup_sylow h earlier F
    (point_core_moves_plane_of_component C hm)
  rw [←point_parabolics_generate h earlier F,←hp]
  simp only [sup_assoc, sup_left_comm (T : Subgroup G) (F.Li L 1), sup_idem]

/-- The escaping join cannot be generated from V by the two-residual of Y.
This is the original I₂-normalization contradiction of 12.9.7. -/
theorem plane_escape_span_ne_residual_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hfail : ¬ centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    conjugateSpanBy V (planeJoinResidual F C) ≠
      F.UH (planeCentralizerJoin F C ⊔ F.Li L 1) := by
  let := h.chosen.elementary
  intro he
  let H := planeCentralizerJoin F C ⊔ F.Li L 1
  have hHz : H ∈ F.Hz L (normalizer (L : Set G)) :=
    (plane_centralizer_escape_join h hn earlier F hab C hfail).2
  have hHU : H ≤ normalizer (F.UH H : Set G) := le_normalizer_conjugateSpanBy V H
  have hIU : planeCoreClosure F ≤ normalizer (F.UH H : Set G) := by
    rw [←he]
    exact normalizes_conjugateSpanBy V (planeJoinResidual F C) (planeCoreClosure F)
      ((planeCoreClosure_le_parabolic h F).trans (F.P_le_seed_normalizer L
        h.chosen.normalizes))
      (planeCoreClosure_normalizes_planeJoinResidual h hn earlier F hab C)
  have hLTU : L ⊔ (T : Subgroup G) ≤ normalizer (F.UH H : Set G) := by
    rw [←planeCoreClosure_point_generate h hn earlier F hab C]
    exact sup_le hIU (sup_le (le_sup_right.trans hHU)
      ((planeCentralizerJoin_placements h F C).1.trans (le_sup_left.trans hHU)))
  have hNM : normalizer (F.UH H : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hJN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique earlier.structural earlier.uniqueness).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN,hJN⟩)
    · exact F.localKernel_UH_isPGroup h.source.simpleQTKE L (normalizer (L : Set G)) H
        (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
        (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩) hHz
    · intro hb
      exact h.chosen.ne_bot (le_bot_iff.mp ((le_conjugateSpanBy V H).trans hb.le))
    · exact hLTU
  exact hHz.2.2 (hHU.trans hNM)

/-- Failure of the original plane bound produces a proper nonzero invariant
subspace of the literal local quotient by V₂. -/
theorem plane_escape_residual_span_proper
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hfail : ¬ centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    F.Vi 2 < conjugateSpanBy V (planeJoinResidual F C) ∧
      conjugateSpanBy V (planeJoinResidual F C) <
        F.UH (planeCentralizerJoin F C ⊔ F.Li L 1) ∧
      planeJoinResidual F C ≤
        normalizer (conjugateSpanBy V (planeJoinResidual F C) : Set G) := by
  have hVE := le_conjugateSpanBy V (planeJoinResidual F C)
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> decide
  refine ⟨lt_of_le_of_ne ((F.le_seed 2).trans hVE) ?_,
    lt_of_le_of_ne (conjugateSpanBy_mono le_rfl ((map_subtype_le _).trans le_sup_left))
      (plane_escape_span_ne_residual_span h hn earlier F hab C hfail),
    le_normalizer_conjugateSpanBy _ _⟩
  intro he
  have hc := card_le_of_le (hVE.trans he.ge)
  have hcard : Nat.card V = 2^n := by simpa only [F.last] using F.card n le_rfl
  rw [hcard,F.card 2 hn2] at hc
  rcases hn with rfl | rfl <;> norm_num at hc

/-- In any coordinates on the original U_H/V₂, the actual two-residual
of Y acts reducibly whenever the plane-centralizer bound fails. -/
theorem plane_escape_section_not_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hfail : ¬ centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (planeCentralizerJoin F C) W)
    (d : Representation.BinaryConjugationSection (planeCentralizerJoin F C)
      (F.UH (planeCentralizerJoin F C ⊔ F.Li L 1)) (F.Vi 2) ρ) :
    ¬ Representation.IsIrreducible (ρ.comp (inclusion
      (show planeJoinResidual F C ≤ planeCentralizerJoin F C from map_subtype_le _))) := by
  intro hi
  let R := planeJoinResidual F C
  let E := conjugateSpanBy V R
  obtain ⟨hVE,hEU,hRE⟩ := plane_escape_residual_span_proper h hn earlier F hab C hfail
  let P : Subrepresentation (ρ.comp (inclusion
      (show R ≤ planeCentralizerJoin F C from map_subtype_le _))) := {
    toSubmodule := d.imageSpace E
    apply_mem_toSubmodule r := by
      intro w hw
      exact d.imageSpace_apply_mem E (inclusion (map_subtype_le _) r)
        (hRE r.property) w hw }
  rcases hi.eq_bot_or_eq_top P with hb | ht
  · have hE : E ≤ F.Vi 2 := by
      intro x hx
      let a : F.UH (planeCentralizerJoin F C ⊔ F.Li L 1) := ⟨x,hEU.le hx⟩
      have hm : (d.coordinates a).toAdd ∈ P :=
        (d.mem_imageSpace_iff E _).mpr ⟨a,hx,rfl⟩
      rw [hb] at hm
      exact (d.coordinates_eq_one_iff a).mp hm
    exact hVE.not_ge hE
  · have he : d.imageSpace E = ⊤ := congrArg Subrepresentation.toSubmodule ht
    exact hEU.not_ge ((d.le_sup_kernel_of_image_top E he).trans (sup_le le_rfl hVE.le))


/-- Construct the actual reducible binary quotient on U_H/V₂, keeping its
literal projection and the original Y- and O²(Y)-actions. -/
theorem plane_escape_reducible_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hfail : ¬ centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    let Y := planeCentralizerJoin F C
    let A := F.UH (Y ⊔ F.Li L 1)
    ∃ hA : IsElementaryAbelian 2 A,
      letI := hA
      ∃ (ρ : Representation (ZMod 2) Y (Additive (A ⧸ (F.Vi 2).subgroupOf A)))
        (d : Representation.BinaryConjugationSection Y A (F.Vi 2) ρ),
        (∀ a : A, (d.coordinates a).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((F.Vi 2).subgroupOf A) a)) ∧
        ¬ Representation.IsIrreducible (ρ.comp (inclusion
          (show planeJoinResidual F C ≤ Y from map_subtype_le _))) := by
  let := h.chosen.elementary
  let Y := planeCentralizerJoin F C
  let H := Y ⊔ F.Li L 1
  let A := F.UH H
  have hHz : H ∈ F.Hz L (normalizer (L : Set G)) :=
    (plane_centralizer_escape_join h hn earlier F hab C hfail).2
  let : IsMulCommutative (conjugateSpanBy V H) :=
    ((h.abelian_source_geometry earlier F).1.mpr hab) H hHz
  let hA : IsElementaryAbelian 2 A := conjugateSpanBy_elementary_of_commutative V H
  refine ⟨hA,?_⟩
  let := hA
  have hAY : A ≤ Y :=
    (F.localKernel_closure h.source.simpleQTKE L (normalizer (L : Set G)) H
      (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
      (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
      hHz).2.2.1.1.trans (planeCentralizerJoin_placements h F C).1
  have hYA : Y ≤ normalizer (A : Set G) := le_sup_left.trans (le_normalizer_conjugateSpanBy V H)
  have hPA : F.Vi 2 ≤ A := (F.le_seed 2).trans (le_conjugateSpanBy V H)
  have hYP : Y ≤ normalizer (F.Vi 2 : Set G) := (planeCentralizerJoin_placements h F C).2
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action Y A (F.Vi 2) hYA hYP inferInstance
  let ρ := Representation.elementaryRepresentation (p := 2) α
  let q := QuotientGroup.mk' ((F.Vi 2).subgroupOf A)
  let d : Representation.BinaryConjugationSection Y A (F.Vi 2) ρ := {
    section_le := hAY
    kernel_le := hPA
    normalized := hYA
    coordinates := {
      toFun a := Multiplicative.ofAdd (Additive.ofMul (q a))
      map_one' := q.map_one
      map_mul' := q.map_mul }
    onto := QuotientGroup.mk'_surjective _
    kernel_eq := QuotientGroup.ker_mk' _
    equivariant y a := by
      change q _ = α y (q a)
      exact (hα y a).symm }
  exact ⟨ρ,d,fun _ => rfl,plane_escape_section_not_irreducible h hn earlier F hab C hfail ρ d⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
