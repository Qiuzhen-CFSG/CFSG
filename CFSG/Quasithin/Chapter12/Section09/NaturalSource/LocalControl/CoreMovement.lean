module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneClosure
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary

/-!
# Plane movement and the original component-core obstruction

The omitted-point parabolic satisfies B.6.1, including its nonnormal Sylow
clause. Thus the actual new I₂ in 12.9.6(2) produces a minimal parabolic,
as well as the previously established S₃ quotient and centralizer rank bound.

If O₂(K₁) fixes the plane, normality propagates fixation to the whole point
span. The source centralizer identity puts this core inside O₂(LT), and
uniqueness of the maximal two-local over LT makes the inclusion strict.
In the literal K₁T/O₂(K₁) quotient, O₂(LT) therefore has nontrivial image
inside the two-core of the image of L₁T. The denominator here is O₂(K₁),
not O₂(K₁T). No model comparison or splitting is assumed.

The remaining model comparisons must exclude this obstruction to prove
12.9.6(1). They and the component, abelianity and other local-control source
premises remain with qt-d-1291-natural-source.

Source: Aschbacher--Smith, 12.9.6, printed pp.861--862 of refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original omitted-point parabolic satisfies the actual B.6.1 condition. -/
theorem parabolic_isMinimalParabolicOver
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) : ChapterB.IsMinimalParabolicOver T (F.P L) := by
  have hTP : (T : Subgroup G) ≤ F.P L := by
    intro t ht
    exact ⟨mem_sup_right ht, mem_iInf.mpr fun i => mem_iInf.mpr fun _ => F.invariant i ht⟩
  have hi := parabolic_sylow_index_three h earlier F
  have hlt : (T : Subgroup G) < F.P L := lt_of_le_of_ne hTP (by
    intro he
    rw [he, relIndex_self] at hi
    contradiction)
  have hcov : (T : Subgroup G) ⋖ F.P L := by
    refine ⟨hlt, ?_⟩
    intro B hTB hBP
    have hiB := relIndex_mul_relIndex (T : Subgroup G) B (F.P L) hTB.le hBP.le
    rw [hi] at hiB
    have hp : ((T : Subgroup G).relIndex B * B.relIndex (F.P L)).Prime := hiB ▸ Nat.prime_three
    rcases Nat.prime_mul_iff.mp hp with ⟨_, hB⟩ | ⟨_, hT⟩
    · exact hBP.not_ge (relIndex_eq_one.mp hB)
    · exact hTB.not_ge (relIndex_eq_one.mp hT)
  apply (ChapterB.isMinimalParabolicOver_iff T (F.P L)).mpr
  refine ⟨⟨hlt, (T : Subgroup G), ⟨le_rfl, hcov⟩, ?_⟩, ?_⟩
  · intro B hB
    by_contra hne
    exact hcov.2 (lt_of_le_of_ne hB.1 (Ne.symm hne)) hB.2.lt
  · intro hn
    let S := T.subtype hTP
    let : (S : Subgroup (F.P L)).Normal := hn
    have heq : (S : Subgroup (F.P L)) = pCore 2 (F.P L) :=
      le_antisymm (le_sSup ⟨inferInstance, S.isPGroup'⟩)
        (pCore_isPGroup.le_sylow_of_normal S)
    obtain ⟨_, ⟨e⟩⟩ := parabolic_plane_quotient h earlier F
    have hiS : (S : Subgroup (F.P L)).index = 3 := hi
    rw [heq, SymmetricThreeTwoCore.core_index e] at hiS
    contradiction

/-- Fixation of the original plane propagates through its point-normalizer span. -/
theorem core_centralizes_point_span_of_plane_fixed
    (h : HigherRankHypothesis K T L V n)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ = ⊥) :
    C.K1.pCoreIn 2 ≤ centralizer (F.U : Set G) := by
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf F.H) :=
    IsElementaryAbelian.subgroupOf ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  let : IsElementaryAbelian 2 (F.tilde V) :=
    IsElementaryAbelian.map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H))
  rw [F.U_eq_plane_span L (by have := h.rank; omega) h.chosen.normalizes
    (fun B hZB hBV hBN => F.invariant_subgroup_of_ambient_natural h.naturalMarking
      (by have := h.rank; omega) B hZB hBV hBN)]
  apply le_centralizer_conjugateSpanBy_of_normalizes
  · exact ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal).trans
      (normalizer_le_normalizer_characteristic_image C.K1 (pCore 2 C.K1))
  · exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm (C.K1.pCoreIn 2) (F.Vi 2)).trans hm)

/-- The original component core is strictly smaller than O₂(LT) if it fixes the plane. -/
theorem component_core_lt_ambient_core_of_plane_fixed
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ = ⊥) :
    C.K1.pCoreIn 2 < (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hn : F.H ≤ normalizer (C.K1.pCoreIn 2 : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal).trans
      (normalizer_le_normalizer_characteristic_image C.K1 (pCore 2 C.K1))
  have hcH : C.K1.pCoreIn 2 ≤ F.H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C.K1)
      ((pCoreIn_le 2 C.K1).trans C.point_le) hn
  have hcT : C.K1.pCoreIn 2 ≤ (T : Subgroup G) := by
    apply hcH.trans
    have ht := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at ht
    exact ht.trans_eq (map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1))
  have hcV := (core_centralizes_point_span_of_plane_fixed h F C hm).trans
    (centralizer_le (le_conjugateSpanBy V F.H))
  have hcQ : C.K1.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← h.centralizer_LT earlier.structural]
    exact le_inf (hcT.trans le_sup_right) hcV
  have hNQ : normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤
      normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal
      (J := L ⊔ (T : Subgroup G))
    · intro N hN hJN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique earlier.structural earlier.uniqueness).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN, hJN⟩)
    · exact isPGroup_pCoreIn 2 _
    · intro he
      exact h.chosen.ne_bot (le_bot_iff.mp (he ▸ h.chosen.le_core))
    · exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  refine lt_of_le_of_ne hcQ ?_
  intro he
  rw [he] at hn
  exact h.flag_escape F earlier.alternatives (hn.trans hNQ)

/-- The component two-core, embedded in its original Sylow join. -/
def componentCoreInJoin {F : InvariantFlag T V n} (C : ComponentGeometry F L) :
    Subgroup (C.K1 ⊔ (T : Subgroup G) : Subgroup G) :=
  (C.K1.pCoreIn 2).subgroupOf (C.K1 ⊔ (T : Subgroup G))

instance componentCoreInJoin_normal {F : InvariantFlag T V n} (C : ComponentGeometry F L) :
    (componentCoreInJoin C).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    ((pCoreIn_le 2 C.K1).trans le_sup_left)).mpr
  exact (sup_le C.point_le (F.invariant 1)).trans
    (((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal).trans
      (normalizer_le_normalizer_characteristic_image C.K1 (pCore 2 C.K1)))

/-- The literal image in K₁T/O₂(K₁), with the source's smaller denominator. -/
def componentCoreImage {F : InvariantFlag T V n} (C : ComponentGeometry F L)
    (A : Subgroup G) :
    Subgroup ((C.K1 ⊔ (T : Subgroup G) : Subgroup G) ⧸ componentCoreInJoin C) :=
  (A.subgroupOf (C.K1 ⊔ (T : Subgroup G))).map (QuotientGroup.mk' (componentCoreInJoin C))

/-- Failure of plane movement leaves a nontrivial normal two-subgroup in
    the literal image of the point residual's Sylow join. -/
theorem ambient_core_image_of_plane_fixed
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ = ⊥) :
    componentCoreImage C ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≠ ⊥ ∧
      componentCoreImage C ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤
        (componentCoreImage C (F.Li L 1 ⊔ (T : Subgroup G))).pCoreIn 2 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let X := C.K1 ⊔ (T : Subgroup G)
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (componentCoreInJoin C)
  have hQT : Q ≤ (T : Subgroup G) := by
    have ht := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using ht
  have hQX : Q ≤ X := hQT.trans le_sup_right
  have hQB : Q ≤ B := hQT.trans le_sup_right
  have hBX : B ≤ X := sup_le_sup_right C.contains _
  have hBN : B ≤ normalizer (Q : Set G) :=
    (sup_le_sup_right ((F.Li_le L 1).trans inf_le_left) _).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hnorm : B.subgroupOf X ≤ normalizer (Q.subgroupOf X : Set X) := by
    intro b hb x
    exact hBN hb (x : G)
  have hnimage : componentCoreImage C B ≤ normalizer (componentCoreImage C Q : Set _) :=
    (map_mono (f := q) hnorm).trans ((Q.subgroupOf X).le_normalizer_map q)
  refine ⟨?_, le_pCoreIn_of_normalizes
    (((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype).map q)
    (map_mono (comap_mono hQB)) hnimage⟩
  intro he
  have hz : Q.subgroupOf X ≤ componentCoreInJoin C := by
    have hz := (map_eq_bot_iff (Q.subgroupOf X)).mp he
    rwa [QuotientGroup.ker_mk'] at hz
  have hQQ : Q ≤ C.K1.pCoreIn 2 := by
    intro x hx
    exact hz (show (⟨x,hQX hx⟩ : X) ∈ Q.subgroupOf X from hx)
  exact (component_core_lt_ambient_core_of_plane_fixed h earlier F C hm).not_ge hQQ

/-- The new I₂ gives the actual minimal parabolic, including its B.6.1
    nonnormal-Sylow clause, as required in 12.9.6(2). -/
theorem planeCoreClosure_minimalParabolic_of_component_movement
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥) :
    ChapterB.IsMinimalParabolicOver T (planeCoreClosure F ⊔ (T : Subgroup G)) := by
  rw [planeCoreClosure_sup_sylow h earlier F (point_core_moves_plane_of_component C hm)]
  exact parabolic_isMinimalParabolicOver h earlier F

/-- Full 12.9.6(2–3), conditional only on the movement in 12.9.6(1).
The minimal-parabolic assertion is the actual B.6.1 predicate. -/
theorem plane_local_control_with_minimal_parabolic
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥) :
    ((planeCoreClosure F).subgroupOf (F.Gi 2)).Normal ∧
      planeCoreClosure F ⊔ (T : Subgroup G) = F.P L ∧
      ChapterB.IsMinimalParabolicOver T (planeCoreClosure F ⊔ (T : Subgroup G)) ∧
      (T : Subgroup G).relIndex (planeCoreClosure F ⊔ (T : Subgroup G)) = 3 ∧
      (planeCoreClosure F).pCoreIn 2 = planeCoreClosure F ⊓ centralizer (F.Vi 2 : Set G) ∧
      Nonempty (((planeCoreClosure F) ⧸ pCore 2 (planeCoreClosure F)) ≃* Equiv.Perm (Fin 3)) ∧
      primeRank 3 (centralizer (F.Vi 2 : Set G)) ≤ 1 := by
  obtain ⟨hn, he, hi, hk, hq, hr⟩ := plane_local_control_of_component_movement h earlier F C hm
  exact ⟨hn, he, planeCoreClosure_minimalParabolic_of_component_movement h earlier F C hm,
    he.symm ▸ hi, hk, hq, hr⟩

/-- The original source setup either moves the plane or yields the strict
core inclusion and the nontrivial two-core image used in the model comparison.
No core or quotient witness is added to the source hypotheses. -/
theorem plane_movement_or_core_obstruction
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥ ∨
      C.K1.pCoreIn 2 ≤ centralizer (F.U : Set G) ∧
      C.K1.pCoreIn 2 < (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      componentCoreImage C ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≠ ⊥ ∧
      componentCoreImage C ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤
        (componentCoreImage C (F.Li L 1 ⊔ (T : Subgroup G))).pCoreIn 2 := by
  by_cases hm : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ = ⊥
  · exact Or.inr ⟨core_centralizes_point_span_of_plane_fixed h F C hm,
      component_core_lt_ambient_core_of_plane_fixed h earlier F C hm,
      ambient_core_image_of_plane_fixed h earlier F C hm⟩
  · exact Or.inl hm

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
