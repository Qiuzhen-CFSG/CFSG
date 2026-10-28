module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Omega
public import CFSG.Quasithin.Chapter13.Section05.A5Source.CrossModule
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# Common centralizers and center bounds for the original A₅ pair

Let K supplement the original Sylow subgroup to an outside H. A nontrivial
subgroup of T centralized by both L and K would have its normalizer in
N_G(L), by the original unique maximal two-local overgroup. Thus their
common Sylow centralizer is trivial.

When both original natural modules are moved by J(T), the two proved
omega-center splittings have disjoint fixed summands. Product cardinalities
then bound Ω₁Z(T) by four and Ω₁Z(J(T)) by sixteen. Each component fixes at
most two elements of the first center and four of the second. The full
H-orbit of Ω₁Z(T) splits as the chosen K-module plus its H-fixed summand,
so it has order sixteen or thirty-two.

These are ambient consequences of the original pair, using 13.2.4(2b)
and uniqueness 1.2.7, not a numerical assertion about n(H). The actual
nonsolvable residual application is in SourceAssembly/NonsolvableCenters.
Source: Aschbacher--Smith, printed pp.506--507,879--880; the remaining
nonsolvable exclusion in 13.2.8(1) still belongs to the assembly owner.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The two components have no common Sylow centralizer. -/
theorem common_sylow_centralizer_eq_bot
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hjoin : K ⊔ (T : Subgroup G) = H) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) ⊓ centralizer (K : Set G) = ⊥ := by
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G) ⊓ centralizer (K : Set G)
  by_contra hn
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf ((le_inf (T : Subgroup G).le_normalizer
      (d.normalizes_L.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf)
      (hTK.trans (normalizer_le_normalizer_centralizer K))).trans
        inf_normalizer_le_normalizer_inf
  have hLC : L ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (L : Set G) from
      inf_le_left.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hKC : K ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (K : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hN := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    (T.isPGroup'.to_le (show C ≤ (T : Subgroup G) from inf_le_left.trans inf_le_left))
    hn (sup_le hLC hTC)
  exact hH.1.2 ((hjoin.ge.trans (sup_le hKC hTC)).trans hN)

omit d in
private theorem card_bounds_of_disjoint_fixed_parts
    (E A B P Q : Subgroup G) [IsMulCommutative E]
    (hA : A ≤ E) (hB : B ≤ E) (hP : P ≤ E) (hQ : Q ≤ E)
    (hEA : E = A ⊔ P) (hEB : E = B ⊔ Q)
    (hdA : Disjoint A P) (hdB : Disjoint B Q) (hd : Disjoint A B) :
    Nat.card A ≤ Nat.card Q ∧ Nat.card B ≤ Nat.card P ∧
      Nat.card E ≤ Nat.card P * Nat.card Q := by
  have hn (X Y : Subgroup G) (hX : X ≤ E) (hY : Y ≤ E) :
      Y ≤ normalizer (X : Set G) :=
    (hY.trans ((le_centralizer E).trans (centralizer_le hX))).trans
      (Subgroup.centralizer_le_normalizer _)
  have ha : Nat.card E = Nat.card A * Nat.card P := by
    conv_lhs => rw [hEA]
    exact card_sup_eq_mul_of_normalizes_of_disjoint A P (hn A P hA hP) hdA
  have hb : Nat.card E = Nat.card B * Nat.card Q := by
    conv_lhs => rw [hEB]
    exact card_sup_eq_mul_of_normalizes_of_disjoint B Q (hn B Q hB hQ) hdB
  have hab : Nat.card A * Nat.card B ≤ Nat.card E := by
    rw [←card_sup_eq_mul_of_normalizes_of_disjoint A B (hn A B hA hB) hd]
    exact card_le_of_le (sup_le hA hB)
  have hapos : 0 < Nat.card A := Nat.card_pos
  have hbpos : 0 < Nat.card B := Nat.card_pos
  have hAQ : Nat.card A ≤ Nat.card Q := by nlinarith
  have hBP : Nat.card B ≤ Nat.card P := by nlinarith
  refine ⟨hAQ,hBP,?_⟩
  rw [ha]
  nlinarith

/-- The two original splittings bound the full Sylow omega-center. -/
theorem original_pair_omega_bounds
    (e : Section05.A5Source.Context T K W W₁ W₂ W₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    Nat.card (omegaOneCenterAmbient (T : Subgroup G)) ≤ 4 ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) ≤ 2 ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) : Subgroup G) ≤ 2 := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let A := Z ⊓ centralizer (L : Set G)
  let B := Z ⊓ centralizer (K : Set G)
  let := omegaOneCenterAmbient_elementaryAbelian (T : Subgroup G)
  have hZd : Z = A ⊔ V₁ := (omega_decomposition_of_thompson_moves d hJd).trans (sup_comm _ _)
  have hZe : Z = B ⊔ W₁ := (omega_decomposition_of_thompson_moves e hJe).trans (sup_comm _ _)
  have hAZ : A ≤ Z := inf_le_left
  have hBZ : B ≤ Z := inf_le_left
  have hdA : Disjoint A V₁ := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact d.flag.module.fixed_eq_bot.le
      ⟨(d.flag.one_le_two.trans d.flag.two_le_V) hx.2,hx.1.2⟩
  have hdB : Disjoint B W₁ := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact e.flag.module.fixed_eq_bot.le
      ⟨(e.flag.one_le_two.trans e.flag.two_le_V) hx.2,hx.1.2⟩
  have hd : Disjoint A B := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact (common_sylow_centralizer_eq_bot d hH e.normalizes_L hjoin).le
      ⟨⟨((mem_omegaOneCenterAmbient_iff _ _).mp hx.1.1).1,hx.1.2⟩,hx.2.2⟩
  obtain ⟨ha,hb,hz⟩ := card_bounds_of_disjoint_fixed_parts Z A B V₁ W₁ hAZ hBZ
    (le_sup_right.trans hZd.ge) (le_sup_right.trans hZe.ge) hZd hZe hdA hdB hd
  simp only [d.flag.one_card,e.flag.one_card] at ha hb hz
  exact ⟨hz,ha,hb⟩

private theorem thompson_fixed_card_le_four
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    Nat.card (V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) : Subgroup G) ≤ 4 := by
  let F := V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hTJ : (T : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  have h8 : Nat.card F ≠ 8 := d.centralizer_intersection_ne_eight hJT hTJ
  have h16 : Nat.card F ≠ 16 := by
    intro hc
    have he : F = V := eq_of_le_of_card_ge inf_le_left (by rw [hc,d.module_card])
    exact hJ (le_centralizer_iff.mp (he.ge.trans inf_le_right))
  have hd : Nat.card F ∣ 16 := by
    rw [←d.module_card]
    exact card_dvd_of_le (show F ≤ V from inf_le_left)
  have hb : Nat.card F ≤ 16 := Nat.le_of_dvd (by decide) hd
  generalize Nat.card F = n at h8 h16 hd hb ⊢
  interval_cases n <;> norm_num at *

/-- The same pair bounds the full Thompson omega-center and both fixed parts. -/
theorem original_pair_alpha_bounds
    (e : Section05.A5Source.Context T K W W₁ W₂ W₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    Nat.card (ChapterB.thompsonAlpha (T : Subgroup G)) ≤ 16 ∧
      Nat.card (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) ≤ 4 ∧
      Nat.card (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (K : Set G) : Subgroup G) ≤ 4 := by
  let E := ChapterB.thompsonAlpha (T : Subgroup G)
  let A := E ⊓ centralizer (L : Set G)
  let B := E ⊓ centralizer (K : Set G)
  let P := V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  let Q := W ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  let : IsElementaryAbelian 2 E :=
    omegaOneCenterAmbient_elementaryAbelian (elementaryAbelianMaxJ (T : Subgroup G))
  have hEd : E = A ⊔ P := local_alpha_decomposition d hJd
  have hEe : E = B ⊔ Q := local_alpha_decomposition e hJe
  have hET : E ≤ (T : Subgroup G) := by
    intro x hx
    exact (show elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) from
      sSup_le fun _ hA => hA.1) ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hdA : Disjoint A P := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact d.flag.module.fixed_eq_bot.le ⟨hx.2.1,hx.1.2⟩
  have hdB : Disjoint B Q := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact e.flag.module.fixed_eq_bot.le ⟨hx.2.1,hx.1.2⟩
  have hd : Disjoint A B := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact (common_sylow_centralizer_eq_bot d hH e.normalizes_L hjoin).le
      ⟨⟨hET hx.1.1,hx.1.2⟩,hx.2.2⟩
  obtain ⟨ha,hb,hE⟩ := card_bounds_of_disjoint_fixed_parts E A B P Q inf_le_left inf_le_left
    (le_sup_right.trans hEd.ge) (le_sup_right.trans hEe.ge) hEd hEe hdA hdB hd
  have hP := thompson_fixed_card_le_four d hJd
  have hQ := thompson_fixed_card_le_four e hJe
  exact ⟨hE.trans (Nat.mul_le_mul hP hQ),ha.trans hQ,hb.trans hP⟩

/-- The literal H-orbit has its original natural summand and a fixed summand
of order at most two. In particular its order is sixteen or thirty-two. -/
theorem original_pair_omegaOrbit_bounds
    (e : Section05.A5Source.Context T K W W₁ W₂ W₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    omegaOrbit T H = W ⊔
        (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G)) ∧
      Disjoint W (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G)) ∧
      (Nat.card (omegaOrbit T H) = 16 ∨ Nat.card (omegaOrbit T H) = 32) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hZT : Z ≤ centralizer ((T : Subgroup G) : Set G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hfix : Z ⊓ centralizer (K : Set G) = Z ⊓ centralizer (H : Set G) := by
    apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le
      (show K ≤ H from le_sup_left.trans hjoin.le)))
    apply le_inf inf_le_left
    apply le_centralizer_iff.mp
    exact hjoin.ge.trans (sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans hZT)))
  have hspan : omegaOrbit T H = conjugateSpanBy Z K := by
    change conjugateSpanBy Z H = _
    rw [←hjoin]
    exact conjugateSpanBy_sup_of_normalizes_seed Z K (T : Subgroup G)
      ((le_centralizer_iff.mp hZT).trans (Subgroup.centralizer_le_normalizer _)) e.normalizes_L
  obtain ⟨he,hd⟩ := omega_orbit_splitting_of_thompson_moves e hJe
  change conjugateSpanBy Z K = W ⊔ (Z ⊓ centralizer (K : Set G)) at he
  change Disjoint W (Z ⊓ centralizer (K : Set G)) at hd
  rw [hfix] at he hd
  have hU : omegaOrbit T H = W ⊔ (Z ⊓ centralizer (H : Set G)) := hspan.trans he
  have hc : Nat.card (Z ⊓ centralizer (H : Set G) : Subgroup G) ≤ 2 := by
    rw [←hfix]
    exact (original_pair_omega_bounds d e hH hjoin hJd hJe).2.2
  have hpos : 0 < Nat.card (Z ⊓ centralizer (H : Set G) : Subgroup G) := Nat.card_pos
  have hcard : Nat.card (omegaOrbit T H) = 16 *
      Nat.card (Z ⊓ centralizer (H : Set G) : Subgroup G) := by
    rw [hU,card_sup_eq_mul_of_normalizes_of_disjoint W _ ?_ hd,e.module_card]
    exact ((inf_le_right.trans (centralizer_le
      (e.chosen.le_sylow.trans hH.1.1.2)))).trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨hU,hd,?_⟩
  omega

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

