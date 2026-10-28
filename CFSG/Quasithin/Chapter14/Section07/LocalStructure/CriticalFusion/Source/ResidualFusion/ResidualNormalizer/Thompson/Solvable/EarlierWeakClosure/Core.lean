module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.EarlierWeakClosure.Geometry
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import Theory.ElementaryAbelian.Injective


/-!
# The first weak-closure clause of 14.7.31

G.2.2 on the actual point-parabolic join gives [V,R₁] ≤ V₁. Consequently
each vector of V centralizes a hyperplane of any conjugate contained in R₁.
Hyperplane centralizer control and the commuting-intersection criterion for
abelian U exclude noncentral conjugates. Thus W₀(R₁,V) lies in O₂(LT).
The conjugacy-family span agrees with the span in that normal two-core;
uniqueness of the maximal two-local over LT controls its ambient normalizer.

The source assembly discharges 1.2.7 from its proved known-simple theorem.
The structural 12.2.2 input remains owned by qt-d-1222-source, with final
14.7.75 assembly owned by qt-d-14775-source.

Source: Aschbacher–Smith, Lemma 14.7.31(1), printed p.1055, PDF p.1072;
12.8.6(2–3), printed pp.850–851; G.2.2, printed p.332.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.EarlierWeakClosure
open Chapter12.Section08 Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- G.2.2 on L₁T, with its actual embedded two-core R₁. -/
theorem point_core_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) : ⁅V, F.Ri L 1⁆ ≤ F.Vi 1 := by
  let := h.chosen.elementary
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  have hJH : J ≤ F.H :=
    sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have hc : Nat.card (F.Vi 1) = 2 := by simpa only [pow_one] using F.card 1 (by decide)
  have hp : F.Vi 1 ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hc
    omega
  have hpJ : F.Vi 1 ≤ J := (F.le_seed 1).trans (h.chosen.le_sylow.trans le_sup_right)
  have hpQ : F.Vi 1 ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsPGroup.of_card (n := 1) (by simpa using hc)) hpJ hJH
  have hQ : J.pCoreIn 2 ≠ ⊥ := fun he => hp (le_bot_iff.mp (he ▸ hpQ))
  have hJ : J ∈ F.Hz L ⊥ := by
    refine ⟨⟨hQ, ?_⟩, hJH, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact mem_sup_left hx
      · exact mem_sup_right hx
    · intro he
      exact hp (le_bot_iff.mp (hpJ.trans he))
  have hs := F.localKernel_hypothesis h.source.simpleQTKE L ⊥ J (by decide)
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  have hh := hs.commutator_U_core_le_point
  change ⁅conjugateSpanBy V J, J.pCoreIn 2⁆ ≤ F.Vi 1 at hh
  exact (commutator_mono (le_conjugateSpanBy V J) le_rfl).trans hh

/-- The abelian point span forces intersecting seed conjugates to commute. -/
theorem intersecting_conjugates_commute
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (hU : IsMulCommutative F.U) (g : G)
    (hne : V ⊓ conjugate V g ≠ ⊥) : ⁅V, conjugate V g⁆ = ⊥ := by
  let := h.chosen.elementary
  have hc : Nat.card (F.Vi 1) = 2 := by simpa only [pow_one] using F.card 1 (by decide)
  have hp : F.Vi 1 ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hc
    omega
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp hp
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hzV := F.le_seed 1 z.property
  have hpoint : F.Vi 1 = zpowers (z : G) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr z.property) ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hzV) hz1, hc]
  apply ((F.abelian_U_iff_intersections_commute (by decide) z hpoint hz1 ?_).mp hU) g hne
  intro x hx hx1
  obtain ⟨l, hl, he⟩ := h.vector_transitive hzV hx hz1 hx1
  exact ⟨l, h.chosen.normalizes hl, he⟩

omit [Finite G] in
/-- A central order-two displacement makes each vector centralize a hyperplane. -/
private theorem normalizes_of_point_commutator
    (C P : Subgroup G) [IsMulCommutative P]
    (hC : Nat.card C = 8) (hP : Nat.card P = 2)
    (hCP : C ≤ centralizer (P : Set G)) (v : G)
    (hcomm : ∀ c ∈ C, ⁅c, v⁆ ∈ P)
    (hhyper : ∀ D ≤ C, Nat.card D = 4 → centralizer (D : Set G) ≤ normalizer (C : Set G)) :
    v ∈ normalizer (C : Set G) := by
  let f : C →* P := {
    toFun := fun c => ⟨⁅(c : G), v⁆, hcomm c c.property⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅(a : G) * (b : G), v⁆ = ⁅(a : G), v⁆ * ⁅(b : G), v⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        ← hCP a.property _ (hcomm b b.property), mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm (⟨⁅(b : G), v⁆, hcomm b b.property⟩ : P)
        (⟨⁅(a : G), v⁆, hcomm a a.property⟩ : P)) }
  let D := f.ker.map C.subtype
  have hDC : D ≤ C := map_subtype_le _
  have hvD : v ∈ centralizer (D : Set G) := by
    rintro x ⟨c, hc, rfl⟩
    have he : ⁅(c : G), v⁆ = 1 := congrArg Subtype.val (show f c = 1 from hc)
    exact commutatorElement_eq_one_iff_mul_comm.mp he
  have hidx : f.ker.index = 1 ∨ f.ker.index = 2 := by
    rw [index_ker]
    have hd := f.range.card_subgroup_dvd_card
    rw [hP] at hd
    exact (Nat.dvd_prime Nat.prime_two).mp hd
  rcases hidx with hidx | hidx
  · have hker : f.ker = ⊤ := index_eq_one.mp hidx
    have hDCeq : D = C := by simp only [D, hker, ← MonoidHom.range_eq_map, range_subtype]
    exact Subgroup.centralizer_le_normalizer _ (hDCeq ▸ hvD)
  · apply hhyper D hDC _ hvD
    have he := f.ker.index_mul_card
    rw [hidx, hC] at he
    change Nat.card (f.ker.map C.subtype) = 4
    rw [card_map_of_injective C.subtype_injective]
    omega

/-- Hyperplane control excludes every noncentral conjugate contained in R₁. -/
theorem conjugate_in_R_centralizes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hU : IsMulCommutative F.U)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (g : G) (hg : conjugate V g ≤ F.Ri L 1) :
    conjugate V g ≤ centralizer (V : Set G) := by
  let := h.chosen.elementary
  by_cases hinter : V ⊓ conjugate V g = ⊥
  · have hRT : F.Ri L 1 ≤ (T : Subgroup G) :=
      (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
        (map_subgroupOf_eq_of_le le_sup_right)
    have hCN : conjugate V g ≤ normalizer (V : Set G) :=
      hg.trans (hRT.trans (h.sylow_normalizes_seed structural))
    have hCP : conjugate V g ≤ centralizer (F.Vi 1 : Set G) :=
      (hg.trans (hRT.trans (F.invariant 1))).trans
        (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
    have hdisp : ⁅conjugate V g, V⁆ ≤ F.Vi 1 := by
      rw [commutator_comm]
      exact (commutator_mono le_rfl hg).trans (point_core_commutator h structural F)
    let : IsElementaryAbelian 2 (F.Vi 1) :=
      IsElementaryAbelian.of_injective (inclusion (F.le_seed 1)) (inclusion_injective _)
    have hVN : V ≤ normalizer (conjugate V g : Set G) := by
      intro v hv
      apply normalizes_of_point_commutator (conjugate V g) (F.Vi 1)
        (by rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, h.seed_card]; norm_num)
        (by simpa using F.card 1 (by decide)) hCP v
        (fun c hc => hdisp (commutator_mem_commutator hc hv))
      exact fun D hD hc => hyperplane_centralizer h structural F hplane g D hD hc
    apply le_centralizer_iff.mpr
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hinter]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hCN)
      (le_normalizer_iff_commutator_le_right.mp hVN)
  · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (intersecting_conjugates_commute h F hU g hinter))

/-- Clause (1): core containment, LT-normality, and the full ambient normalizer bound. -/
theorem clause_one
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hU : IsMulCommutative F.U)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    ChapterE.indexedWeakClosure V (F.Ri L 1) 0 ≤ L ⊔ (T : Subgroup G) ∧
      L ⊔ (T : Subgroup G) ≤
        normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) ∧
      normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) ≤
        normalizer (L : Set G) := by
  let := h.chosen.elementary
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQN : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hJLT : F.Li L 1 ⊔ (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) :=
    sup_le_sup_right ((F.Li_le L 1).trans inf_le_left) _
  have hQR : Q ≤ F.Ri L 1 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) (hQT.trans le_sup_right)
      (hJLT.trans hQN)
  have hVQ : V ≤ Q := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    (h.chosen.le_sylow.trans le_sup_right)
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural))
  have hRLT : F.Ri L 1 ≤ L ⊔ (T : Subgroup G) := (pCoreIn_le 2 _).trans hJLT
  have hWC : ChapterE.indexedWeakClosure V (F.Ri L 1) 0 ≤ centralizer (V : Set G) := by
    rw [ChapterE.weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro C hC
    obtain ⟨g, rfl, hg⟩ := (ChapterE.mem_gamma_zero_iff V (F.Ri L 1) C).mp hC
    simpa only [conjugate, inv_inv] using conjugate_in_R_centralizes h structural F hU
      hplane g⁻¹ (by simpa only [conjugate, inv_inv] using hg)
  have hWQ : ChapterE.indexedWeakClosure V (F.Ri L 1) 0 ≤ Q :=
    (le_inf ((ChapterE.indexedWeakClosure_le _ _ _).trans hRLT) hWC).trans
      (h.centralizer_LT structural).le
  have heq : ChapterE.indexedWeakClosure V (F.Ri L 1) 0 =
      ChapterE.indexedWeakClosure V Q 0 :=
    le_antisymm (SubgroupFamily.span_le_span_of_span_le hWQ)
      (ChapterE.weakClosure_mono V 0 hQR)
  have hn : L ⊔ (T : Subgroup G) ≤
      normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) := by
    rw [heq]
    exact hQN.trans (ChapterE.normalizer_le_weakClosure_normalizer V Q 0)
  refine ⟨hWQ.trans (pCoreIn_le 2 _), hn, ?_⟩
  apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G)) _
    ((isPGroup_pCoreIn 2 _).to_le hWQ) _ hn
  · intro N hN hJN
    exact Set.mem_singleton_iff.mp ((h.maximal_unique structural uniqueness).2 ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN, hJN⟩)
  · intro he
    exact h.chosen.ne_bot (le_bot_iff.mp (he ▸
      ChapterE.self_le_weakClosure_zero (hVQ.trans hQR)))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.EarlierWeakClosure
