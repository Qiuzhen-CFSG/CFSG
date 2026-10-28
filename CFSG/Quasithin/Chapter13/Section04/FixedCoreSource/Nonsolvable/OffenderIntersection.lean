module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Rank

/-!
# The ambient centralizer step in the final nonsolvable contradiction

Normalizer fusion and the fixed-generator centralizer make V the unique
conjugate containing its distinguished fixed point. For W = V_H, point
fusion from 13.4.17(4) therefore puts W ∩ Vʸ in the conjugate fixed line.
The no-transvection assertion of 13.4.2(4) forces W ∩ N_G(Vʸ) to centralize
Vʸ. The actual global rank parameter then controls all centralizers of
subgroups of Vʸ of corank at most two.

This is the terminal consumer of the earlier geometry. Construction of W,
its point fusion, and the moving conjugate remains with
qt-d-1341-nonsolvable-source, as does the 13.4.12 uniqueness premise needed
by the rank bound. Final ambient recognition belongs to
qt-d-1341-fixed-core-source. Source: Aschbacher–Smith, printed p.915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
namespace CoreMarking
variable {D : ChosenModule T L V} (m : CoreMarking D)

/-- The distinguished fixed generator belongs to only one conjugate of V. -/
theorem conjugate_eq_of_constant_mem
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (g : G) (hg : m.constant.val ∈ V.conjBy g) : V.conjBy g = V := by
  obtain ⟨c, hc, he⟩ := (element_fusion_iff_centralizer_incidence V m.constant.val).mp
    (hfusion m.constant m.constant_ne_one) g hg
  rw [← he]
  apply mem_normalizer_iff_map_conj_eq.mp
  rw [← normalizer_component_eq_module h structural D m]
  exact (fixed_generator_centralizer h structural D m
    ⟨m.constant.property, m.constant_fixed⟩
    (fun he => m.constant_ne_one (Subtype.ext he))) ▸ hc

/-- Equal conjugates of V have equal distinguished fixed generators. -/
theorem constant_conj_eq_of_module_conj_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (g y : G) (he : V.conjBy g = V.conjBy y) :
    MulAut.conj g m.constant.val = MulAut.conj y m.constant.val := by
  have hn := mem_normalizer_iff_map_conj_eq.mpr (conjBy_inv_mul_cancel V he)
  have hc : g⁻¹ * y ∈ centralizer ({m.constant.val} : Set G) := by
    rw [fixed_generator_centralizer h structural D m
      ⟨m.constant.property, m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he)),
      normalizer_component_eq_module h structural D m]
    exact hn
  have hf : MulAut.conj (g⁻¹ * y) m.constant.val = m.constant.val :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc)
  have hh := congrArg (MulAut.conj g) hf
  simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc,
    mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel_right,
    mul_inv_cancel, inv_mul_cancel, one_mul, mul_one] using hh.symm

/-- If the nonidentity points of W are fused to the distinguished generator,
its intersection with a returning conjugate has only that conjugate's fixed point. -/
theorem intersection_le_conjugate_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (W : Subgroup G) (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) : W ⊓ V.conjBy y ≤ (V ⊓ centralizer (L : Set G)).conjBy y := by
  intro w hw
  by_cases hw1 : w = 1
  · simpa only [hw1] using (one_mem ((V ⊓ centralizer (L : Set G)).conjBy y))
  obtain ⟨g, hg⟩ := isConj_iff.mp (hpoints w hw.1 hw1)
  have hm : m.constant.val ∈ V.conjBy (g⁻¹ * y) := by
    rw [conjBy_mul]
    refine ⟨w, hw.2, ?_⟩
    rw [← hg]
    simp [mul_assoc]
  have hh := m.conjugate_eq_of_constant_mem h structural hfusion (g⁻¹ * y) hm
  have he : V.conjBy y = V.conjBy g := by
    have he := congrArg (fun X : Subgroup G => X.conjBy g) hh
    simpa only [conjBy_conjBy, mul_inv_cancel_left] using he
  have hwy : w = MulAut.conj y m.constant.val :=
    hg.symm.trans (m.constant_conj_eq_of_module_conj_eq h structural g y he.symm)
  rw [hwy]
  exact ⟨m.constant.val, ⟨m.constant.property, m.constant_fixed⟩, rfl⟩


omit [Finite G] in
private theorem conjugate_commutator_eq_bot
    (hkernel : ∀ B : Subgroup G, B ≤ normalizer (V : Set G) →
      ⁅V, B⁆ ≤ V ⊓ centralizer (L : Set G) → ⁅V, B⁆ = ⊥)
    (y : G) (B : Subgroup G) (hB : B ≤ normalizer (V.conjBy y : Set G))
    (hc : ⁅V.conjBy y, B⁆ ≤ (V ⊓ centralizer (L : Set G)).conjBy y) :
    ⁅V.conjBy y, B⁆ = ⊥ := by
  have hn : B.conjBy y⁻¹ ≤ normalizer (V : Set G) := by
    have hh := Subgroup.map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hB
    rw [map_equiv_normalizer_eq] at hh
    change B.conjBy y⁻¹ ≤ normalizer ((V.conjBy y).conjBy y⁻¹ : Set G) at hh
    rwa [conjBy_inv] at hh
  have hh := Subgroup.map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hc
  rw [map_commutator] at hh
  change ⁅(V.conjBy y).conjBy y⁻¹, B.conjBy y⁻¹⁆ ≤
    ((V ⊓ centralizer (L : Set G)).conjBy y).conjBy y⁻¹ at hh
  rw [conjBy_inv, conjBy_inv] at hh
  have he := congrArg (fun X : Subgroup G => X.map (MulAut.conj y).toMonoidHom)
    (hkernel _ hn hh)
  rw [map_commutator, Subgroup.map_bot] at he
  change ⁅V.conjBy y, (B.conjBy y⁻¹).conjBy y⁆ = ⊥ at he
  rwa [conjBy_inv'] at he

/-- The first paragraph on p.915: U = W ∩ N(Vʸ) centralizes A = Vʸ.
The no-fixed-line-transvection premise is precisely 13.4.2(4), and point fusion
is the consequence of 13.4.17(4) used here. -/
theorem terminal_intersection_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hkernel : ∀ B : Subgroup G, B ≤ normalizer (V : Set G) →
      ⁅V, B⁆ ≤ V ⊓ centralizer (L : Set G) → ⁅V, B⁆ = ⊥)
    (W : Subgroup G) (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) (hAW : V.conjBy y ≤ normalizer (W : Set G)) :
    W ⊓ normalizer (V.conjBy y : Set G) ≤ centralizer (V.conjBy y : Set G) := by
  let A := V.conjBy y
  let U := W ⊓ normalizer (A : Set G)
  have hAU : A ≤ normalizer (U : Set G) :=
    (le_inf hAW (A.le_normalizer.trans (normalizer (A : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hc : ⁅A, U⁆ ≤ W ⊓ A :=
    le_inf ((le_normalizer_iff_commutator_le_right.mp hAU).trans inf_le_left)
      (le_normalizer_iff_commutator_le_left.mp (show U ≤ normalizer (A : Set G) from inf_le_right))
  have he := conjugate_commutator_eq_bot hkernel y U inf_le_right
    (hc.trans (m.intersection_le_conjugate_fixed h structural hfusion W hpoints y))
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)

omit m [Finite G] in
/-- The literal centralizer intersections giving the final rank bound and
fixed-space family. It uses r(G,V), without replacing an ambient centralizer
by a centralizer in either local subgroup. -/
theorem terminal_corank_and_fixed_subgroups
    (hr : 3 ≤ ChapterE.globalR V) (W : Subgroup G) (y : G)
    (hU : W ⊓ normalizer (V.conjBy y : Set G) ≤ centralizer (V.conjBy y : Set G))
    (hmove : ¬ W ≤ centralizer (V.conjBy y : Set G)) :
    3 ≤ ChapterE.subgroupCorank (V.conjBy y)
        (V.conjBy y ⊓ centralizer (W : Set G)) ∧
      ∀ B : Subgroup G, B ≤ V.conjBy y →
        ChapterE.subgroupCorank (V.conjBy y) B ≤ 2 →
        W ⊓ centralizer (B : Set G) ≤ W ⊓ centralizer (V.conjBy y : Set G) := by
  have hnot : ¬ W ≤ normalizer (V.conjBy y : Set G) := by
    intro hn
    exact hmove ((le_inf le_rfl hn).trans hU)
  have hr' : 3 ≤ ChapterE.globalR (V.conjBy y) := by
    change 3 ≤ ChapterE.globalR (V.map (MulAut.conj y).toMonoidHom)
    rwa [ChapterE.globalR_map_equiv]
  constructor
  · have hh := ChapterE.globalR_le_corank
      (show V.conjBy y ⊓ centralizer (W : Set G) ≤ V.conjBy y from inf_le_left)
      (fun hn => hnot ((le_centralizer_iff.mpr inf_le_right).trans hn))
    exact_mod_cast hr'.trans hh
  · intro B hBA hB
    have hb : (ChapterE.subgroupCorank (V.conjBy y) B : ℕ∞) < ChapterE.globalR (V.conjBy y) :=
      lt_of_lt_of_le (by exact_mod_cast (show ChapterE.subgroupCorank (V.conjBy y) B < 3 by omega)) hr'
    have hc := ChapterE.centralizer_le_normalizer_of_corank_lt_globalR hBA hb
    exact le_inf inf_le_left ((inf_le_inf_left W hc).trans hU)

end CoreMarking
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
