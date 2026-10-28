module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.OuterCentralizerComparison
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Preserving the point while placing the transferred centralizer

For y in PU outside P, [y,V] is the original point V₁. Consequently
C_{LT}(y) preserves V₁ and lies in H intersect LT = L₁T. This group
normalizes PU. After first moving an inner involution to PU in L,
Sylow conjugacy inside L₁T puts any centralizing two-subgroup of LT
in T and keeps the involution in PU. Both conjugators remain in the
original ambient group.

Source: Aschbacher--Smith, 14.3.33(3), printed p.1005, the placement
preceding the extremal-centralizer comparison.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Each element of PU outside P moves the seed by precisely the original point. -/
theorem core_closure_noncore_seed_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : G) (hy : y ∈ L.pCoreIn 2 ⊔ F.U) (hyP : y ∉ L.pCoreIn 2) :
    ⁅zpowers y, V⁆ = F.Vi 1 := by
  let := h.chosen.elementary
  have hUU := (F.localKernel_commutator_squares h.source.simpleQTKE L
    (normalizer (L : Set G)) (by decide) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives)).1
  have hPC : L.pCoreIn 2 ≤ centralizer (V : Set G) := by
    rw [← h.centralizer_L]
    exact inf_le_right
  have hb : ⁅L.pCoreIn 2 ⊔ F.U,V⁆ ≤ F.Vi 1 :=
    commutator_sup_le_of_relative_normal (T : Subgroup G) _ _ _ _ (F.invariant 1)
      (le_sup_left.trans (core_closure_le_sylow h structural F s)) (closure_le_sylow F s)
      (by rw [commutator_eq_bot_iff_le_centralizer.mpr hPC]; exact bot_le)
      ((commutator_mono le_rfl (le_conjugateSpanBy V F.H)).trans hUU)
  have hc : ⁅zpowers y,V⁆ ≤ F.Vi 1 := (commutator_mono (zpowers_le.mpr hy) le_rfl).trans hb
  have hn : ⁅zpowers y,V⁆ ≠ ⊥ := by
    intro he
    have hyC := (commutator_eq_bot_iff_le_centralizer.mp he) (mem_zpowers y)
    have hyL := (sup_le (pCoreIn_le 2 L) (closure_le_actor h structural alternatives F s hne)) hy
    exact hyP (h.centralizer_L ▸ ⟨hyL,hyC⟩)
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hd : Nat.card (⁅zpowers y,V⁆ : Subgroup G) ∣ 2 := hp ▸ card_dvd_of_le hc
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo
  · exact (hn (Subgroup.card_eq_one.mp hone)).elim
  · exact eq_of_le_of_card_ge hc (by rw [hp,htwo])

/-- The local centralizer of a noncore element of PU preserves the original point. -/
theorem core_closure_noncore_actor_centralizer_le_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : G) (hy : y ∈ L.pCoreIn 2 ⊔ F.U) (hyP : y ∉ L.pCoreIn 2) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer ({y} : Set G) ≤ F.H := by
  intro a ha
  have haV : a ∈ normalizer (V : Set G) :=
    (seed_normalizer_eq_actor_join_sylow h structural alternatives F s hne).symm ▸ ha.1
  have hfix : MulAut.conj a y = y :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp ha.2)
  change a ∈ normalizer (F.Vi 1 : Set G)
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← core_closure_noncore_seed_commutator h structural alternatives F s hne y hy hyP,
    map_commutator, MonoidHom.map_zpowers, mem_normalizer_iff_map_conj_eq.mp haV]
  change ⁅zpowers (MulAut.conj a y),V⁆ = ⁅zpowers y,V⁆
  rw [hfix]

/-- The full point intersection normalizes PU. -/
theorem point_join_sylow_normalizes_core_closure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer ((L.pCoreIn 2 ⊔ F.U : Subgroup G) : Set G) := by
  rw [← point_residual_core h structural alternatives F s hne]
  exact (sup_le (F.Li L 1).le_normalizer (sylow_normalizes_point_residual h structural F)).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F.Li L 1)))

/-- Move an inner involution to PU while placing any centralizing two-subgroup
of LT in T. The second conjugator belongs to L₁T and preserves PU. -/
theorem actor_involution_core_closure_centralizer_placement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : G) (hy : y ∈ L) (hy2 : orderOf y = 2) (hyP : y ∉ L.pCoreIn 2)
    (R : Subgroup G) (hp : IsPGroup 2 R) (hRM : R ≤ L ⊔ (T : Subgroup G))
    (hRC : R ≤ centralizer ({y} : Set G)) :
    ∃ k ∈ L ⊔ (T : Subgroup G), k*y*k⁻¹ ∈ L.pCoreIn 2 ⊔ F.U ∧
      R.map (MulAut.conj k).toMonoidHom ≤ (T : Subgroup G) := by
  let M := L ⊔ (T : Subgroup G)
  let N := F.Li L 1 ⊔ (T : Subgroup G)
  obtain ⟨l,hl,hlPU,hlP⟩ := actor_involution_conjugate_into_core_closure h structural alternatives F s hne y hy hy2 hyP
  let f := MulAut.conj l
  let D := R.map f.toMonoidHom
  have hDM : D ≤ M := by
    rintro _ ⟨a,ha,rfl⟩
    exact M.mul_mem (M.mul_mem (mem_sup_left hl) (hRM ha)) (M.inv_mem (mem_sup_left hl))
  have hDC : D ≤ centralizer ({f y} : Set G) := by
    rintro _ ⟨a,ha,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f a * f y = f y * f a
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hRC ha))
  have hDH : D ≤ F.H := (le_inf hDM hDC).trans
    (core_closure_noncore_actor_centralizer_le_point h structural alternatives F s hne (f y) hlPU hlP)
  have hDN : D ≤ N := by
    dsimp only [N]
    rw [← seed_normalizer_inter_point h structural alternatives F s hne,
      seed_normalizer_eq_actor_join_sylow h structural alternatives F s hne]
    exact le_inf hDM hDH
  obtain ⟨A,hDA⟩ := ((hp.map f.toMonoidHom).comap_subtype (K := N)).exists_le_sylow
  obtain ⟨n,hn⟩ := MulAction.exists_smul_eq N A (T.subtype (show (T : Subgroup G) ≤ N from le_sup_right))
  have hDT : D.map (MulAut.conj (n : G)).toMonoidHom ≤ (T : Subgroup G) := by
    rintro _ ⟨a,ha,rfl⟩
    have hh : MulAut.conj n (⟨a,hDN ha⟩ : N) ∈
        (T.subtype (show (T : Subgroup G) ≤ N from le_sup_right) : Subgroup N) := by
      rw [← hn]
      exact mem_map_of_mem _ (hDA ha)
    exact hh
  have hnPU := point_join_sylow_normalizes_core_closure h structural alternatives F s hne n.property
  have hNM : N ≤ M := sup_le ((F.Li_le L 1).trans inf_le_left |>.trans le_sup_left) le_sup_right
  refine ⟨(n:G)*l,M.mul_mem (hNM n.property) (mem_sup_left hl),?_,?_⟩
  · have hh := (mem_normalizer_iff.mp hnPU (l*y*l⁻¹)).mp hlPU
    simpa only [mul_inv_rev,mul_assoc] using hh
  · have he : (MulAut.conj ((n:G)*l)).toMonoidHom =
        (MulAut.conj (n:G)).toMonoidHom.comp f.toMonoidHom := by
      ext a
      simp only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_inv_rev,mul_assoc]
    rw [he,← map_map]
    exact hDT

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
