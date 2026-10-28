module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentSix
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentAlternatingAction
public import Theory.GroupTheory.PerfectCenterPrimeRank

/-!
# The original alternating component exclusions

The original Sylow E₉ and the marked Sylow-central V-action exclude
ordinary A₇ and A₈. Rank saturation makes the E₉ action faithful when
K-star is centerless, and the permutation centralizer calculation gives
the contradiction. The assembly retains the preceding A₆ exclusions,
condition (*), the same selected component and all rank alternatives.

For the remaining cubic A₇ cover, the literal Sylow-action kernel embeds
in Z(K-star) through H → H/O₂(H). Its action is not faithful, so this
kernel has order three. This proves the actual kernel statement; the
cover's normalizer contradiction is still required. Classical and M₂₂
cover exclusions, the remaining faithful rank-two cases, the rank-one
argument and the universal natural reduction also remain open.
Source: Aschbacher--Smith, proof of 12.6.26, printed pp.832--833.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The actual A₇ or A₈ central quotient forces a kernel in every original Sylow E₉ action. -/
theorem SourceHypothesis.original_alternating_quotient_sylow_not_faithful
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    {n : ℕ} (hnat : n = 7 ∨ n = 8)
    (e : (Nonabelian.Setup.star H c.K ⧸ center (Nonabelian.Setup.star H c.K)) ≃*
      alternatingGroup (Fin n)) (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    ¬ Function.Injective (a.residualSylowAction P) :=
  a.not_faithful_alternating_sylow hnat e P
    (S.original_point_residual_sylow D hZ z hz hTz P).2
    (S.original_action_module_sylow_central D hZ z hz hTV hTz hbound hH hn c a)

/-- Exclude both ordinary alternating rows for the original selected component. -/
theorem SourceHypothesis.original_selectedComponent_not_alternatingSevenEight
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    {n : ℕ} (hnat : n = 7 ∨ n = 8) :
    ¬ Chapter1.Section02.LocalModels.IsAlternating (Nonabelian.Setup.star H c.K) n := by
  rintro ⟨e⟩
  let B := Nonabelian.Setup.star H c.K
  let P : Sylow 3 (D.fullSetup hZ T z).L₁ := Sylow.nonempty.some
  have hc : center B = ⊥ := by
    apply bot_unique
    intro x hx
    have he := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (alternatingGroup (Fin n)) at he
    rw [alternatingGroup.center_eq_bot (by simp; omega),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hr : primeRank 3 c.K = 2 := by
    rw [c.three_rank_eq_star]
    apply le_antisymm
    · exact (_root_.primeRank_le_of_injective 3 B.subtype B.subtype_injective).trans
        (S.original_star_three_rank D hZ z hz hH)
    · rw [primeRank_congr 3 e]
      exact alternatingGroup.TwoThreeCycles.two_le_primeRank (n := n) (by omega)
  let eQ : (B ⧸ center B) ≃* alternatingGroup (Fin n) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e
  exact S.original_alternating_quotient_sylow_not_faithful D hZ z hz hTV hTz hbound hH hn c a hnat eQ P
    (S.original_rank_two_centerless_sylow_faithful D hZ z hz hTz hH c a hr hc P)

/-- The literal quotient map embeds the original Sylow-action kernel in the component center. -/
theorem SourceHypothesis.original_rank_two_sylow_kernel_card_dvd_center
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hr : primeRank 3 c.K = 2) (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    Nat.card (a.residualSylowAction P).ker ∣ Nat.card (center (Nonabelian.Setup.star H c.K)) := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let j : P →* c.localActor := (inclusion (show E.L₁ ≤ c.localActor from
    le_sup_right.trans le_sup_left)).comp (P : Subgroup E.L₁).subtype
  let i := (inclusion a.local_le).comp j
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := (P : Subgroup E.L₁).map E.L₁.subtype
  let F := a.residualSylowAction P
  have hq := (S.original_point_sylow_star D hZ z hz hTz hH P).2.2
  let := (S.original_point_residual_sylow D hZ z hz hTz P).1
  have hmem (x : F.ker) : q (i x.val) ∈ B := by
    have hxker : j x.val ∈ a.action.ker := x.property
    rw [a.kernel] at hxker
    have htC : q (i x.val) ∈ centralizer (B : Set (Nonabelian.Setup.Hstar H)) := hxker
    have hx3 : x.val ^ 3 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x.val.val x.val.property)
    have ht3 : q (i x.val) ^ 3 = 1 := by rw [←map_pow,←map_pow,hx3,map_one,map_one]
    exact B.mem_of_prime_pow_eq_one_of_centralizes_rank_two
      (S.original_star_three_rank D hZ z hz hH) (c.three_rank_eq_star.symm.trans hr) ht3 htC
  have hzmem (x : F.ker) : (⟨q (i x.val),hmem x⟩ : B) ∈ center B := by
    have hxker : j x.val ∈ a.action.ker := x.property
    rw [a.kernel] at hxker
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (hxker b.val b.property)
  let f : F.ker →* center B := {
    toFun := fun x => ⟨⟨q (i x.val),hmem x⟩,hzmem x⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; simp only [OneMemClass.coe_one,map_one]
    map_mul' := fun x y => by apply Subtype.ext; apply Subtype.ext; simp only [Subgroup.coe_mul,map_mul] }
  apply card_dvd_of_injective f
  intro x y he
  have hxA : i x.val ∈ A.subgroupOf H := mem_map_of_mem E.L₁.subtype x.val.property
  have hyA : i y.val ∈ A.subgroupOf H := mem_map_of_mem E.L₁.subtype y.val.property
  have hxy : (⟨i x.val,hxA⟩ : A.subgroupOf H) = ⟨i y.val,hyA⟩ := hq
    (congrArg (fun b : center B => b.val.val) he)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun b : A.subgroupOf H => b.val.val) hxy

/-- In the remaining triple A₇ cover, the original Sylow-action kernel has order three. -/
theorem SourceHypothesis.original_alternatingSevenCover_sylow_kernel_card
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (he : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    Nat.card (a.residualSylowAction P).ker = 3 := by
  obtain ⟨_,⟨ec⟩,⟨e⟩⟩ := he
  let B := Nonabelian.Setup.star H c.K
  have hc : Nat.card (center B) = 3 := by rw [Nat.card_congr ec.toEquiv]; simp
  have hr : primeRank 3 c.K = 2 := by
    rw [c.three_rank_eq_star]
    apply le_antisymm
    · exact (_root_.primeRank_le_of_injective 3 B.subtype B.subtype_injective).trans
        (S.original_star_three_rank D hZ z hz hH)
    · let := c.component.2
      exact two_le_primeRank_of_nontrivial_prime_center (by decide)
        (IsPGroup.of_card (p := 3) (n := 1) hc) (by
          intro heq
          rw [heq,card_bot] at hc
          omega)
  have hd := S.original_rank_two_sylow_kernel_card_dvd_center D hZ z hz hTz hH c a hr P
  rw [hc] at hd
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h1|h3
  · have hk : (a.residualSylowAction P).ker = ⊥ := (Subgroup.card_eq_one.mp h1)
    exact (S.original_alternating_quotient_sylow_not_faithful D hZ z hz hTV hTz hbound hH hn
      c a (Or.inl rfl) e P ((MonoidHom.ker_eq_bot_iff _).mp hk)).elim
  · exact h3

/-- Select the original component and action with condition (*), all rank alternatives, the ordinary A₆/A₇/A₈ exclusions and the exact cubic A₇ kernel. -/
theorem SourceHypothesis.original_selectedComponent_without_alternating_rank_two
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    ∃ c : (D.fullSetup hZ T z).SelectedComponent H, ∃ a : c.ActionMarking,
      let A := (((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let C := centralizer (U : Set a.action.range)
      (Nat.card U = 2 ∧ 3 ∣ Nat.card A ∧
        A.subgroupOf C ≤ (pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C)) ∧
        ∃ R : Sylow 2 a.action.range, U ≤ (R : Subgroup a.action.range) ∧
          U ≤ centralizer (R : Set a.action.range)) ∧
      (primeRank 3 c.K = 1 ∨ (primeRank 3 c.K = 2 ∧
        ∀ P : Sylow 3 (D.fullSetup hZ T z).L₁,
          Function.Injective (a.residualSylowAction P) ∨
            (Nonempty (center (Nonabelian.Setup.star H c.K) ≃* Multiplicative (ZMod 3)) ∧
              Chapter1.Section02.LocalModels.ThreeCoverModel (Nonabelian.Setup.star H c.K)))) ∧
      (∀ n : ℕ, 6 ≤ n → n ≤ 8 →
        ¬ Chapter1.Section02.LocalModels.IsAlternating (Nonabelian.Setup.star H c.K) n) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 6 ∧
      (Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7 →
        ∀ P : Sylow 3 (D.fullSetup hZ T z).L₁, Nat.card (a.residualSylowAction P).ker = 3) := by
  obtain ⟨c,a,hc,hr,h6,h6c⟩ := S.original_selectedComponent_without_six D hZ z hz hTV hTz hbound hns hH hn
  refine ⟨c,a,hc,hr,?_,h6c,?_⟩
  · intro n hl hu
    have hcases : n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hcases with rfl|h78
    · exact h6
    · exact S.original_selectedComponent_not_alternatingSevenEight D hZ z hz hTV hTz hbound hH hn c a h78
  · intro he P
    exact S.original_alternatingSevenCover_sylow_kernel_card D hZ z hz hTV hTz hbound hH hn c a he P

end CFSG.Quasithin.Chapter12.Section06
