module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceDoubledNatural
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceThompson
public import Theory.PrimeRank

/-!
# Source-faithful component cases 13.6.17--23

These declarations are the source-facing extensions of the older conditional
helpers in `ComponentElimination`.  Every input below is an earlier theorem
or a concrete module/action calculation. In particular, ranks are expressed
by `primeRank`, the doubled-natural branch has an actual binary module and
parabolic action, and the two residual conventions in the final paragraph
are kept distinct.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, printed
pp.930--933.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source

variable {G : Type*} [Group G]

/-- Earlier A.4.9 and 13.6.3 data used in the noncentrality argument. The
second field is universally quantified over the actual components produced by
the transfer, so it does not package the desired noncentrality conclusion. -/
structure NoncentralityInput (K : Subgroup G) (z a v : G) where
  transfer : (∃ g : G, a = MulAut.conj g z) → K ≤ Gv a → ∃ K₁ : Subgroup G,
    IsComponentIn (Gv v) K₁ ∧ K₁ ≤ Gv a
  forbidden : ∀ {K₁ : Subgroup G}, IsComponentIn (Gv v) K₁ →
    K₁ ≤ Gv a → False

/-- Lemma 13.6.17 for the actual conjugate `a = z^g`. -/
theorem noncentral_of_central_conjugate
    {z a v : G} {K : Subgroup G} (d : NoncentralityInput K z a v)
    (hconj : ∃ g : G, a = MulAut.conj g z) : ¬ K ≤ Gv a := by
  intro hK
  obtain ⟨K₁, hK₁, hK₁a⟩ := d.transfer hconj hK
  exact d.forbidden hK₁ hK₁a

/-- The Borel centralization contradiction in 13.6.18. `hBorel` is the
concrete block/Borel action output, while `d` is the earlier transfer. -/
theorem exclude_l2_even_source
    {z a v : G} {K : Subgroup G} (d : NoncentralityInput K z a v)
    (hconj : ∃ g : G, a = MulAut.conj g z)
    (n : ℕ) (hmodel : ChapterC.IsL2EvenBlock K n)
    (hBorel : ChapterC.IsL2EvenBlock K n → K ≤ Gv a) : False :=
  (noncentral_of_central_conjugate d hconj) (hBorel hmodel)

/-- Lemma 13.6.19: the maximal-parabolic calculation supplies a genuine
component and genuine even-field L₂ block, which the earlier 13.6.16(2)
obstruction rejects. -/
theorem exclude_higher_field_source
    {v : G} {_K : Subgroup G} (_case : HigherFieldCase _K)
    (hparabolic : ∃ K₁ : Subgroup G, IsComponentIn (Gv v) K₁ ∧
      ∃ n : ℕ, 1 < n ∧ ChapterC.IsL2EvenBlock K₁ n)
    (hblock : ∀ {K₁ : Subgroup G}, IsComponentIn (Gv v) K₁ →
      ∀ {n : ℕ}, 1 < n → ¬ ChapterC.IsL2EvenBlock K₁ n) : False := by
  obtain ⟨K₁, hK₁, n, hn, hL₂⟩ := hparabolic
  exact hblock hK₁ hn hL₂

/-- The source m₃(K)=2 alternative, with the genuine rank predicate. -/
theorem lv_le_of_primeRank_three_eq_two
    {L : Subgroup G} {v : G} {K : Subgroup G}
    (hrank : primeRank 3 K = 2)
    (hA318 : primeRank 3 K = 2 → Lv L v ≤ K) : Lv L v ≤ K :=
  hA318 hrank

/-- The source split-module alternative retains actual summands, their
equivariant parabolic action, and the generated commutator subgroup. -/
structure DoubledNaturalSource (L V K : Subgroup G) (v : G) where
  moduleEquiv : Nonempty (K ≃* Multiplicative (BinaryLinearThree.Vector ×
    BinaryLinearThree.Vector))
  parabolic : Subgroup G
  parabolic_normalizes_K : parabolic ≤ normalizer (K : Set G)
  actor : parabolic →* Matrix.PSL3Two.lineParabolicSL
  actor_surjective : Function.Surjective actor
  action_equivariant : ∀ p : parabolic, ∀ x : K,
    ∀ e : (K ≃* Multiplicative
      (BinaryLinearThree.Vector × BinaryLinearThree.Vector)),
      e (ComponentSelection.conjugationAction K parabolic
        parabolic_normalizes_K p x) =
      Multiplicative.ofAdd ((BinaryLinearThree.W.prod BinaryLinearThree.W)
        (actor p : BinaryLinearThree.Group)
        (Multiplicative.toAdd (e x)))
  split_points : ∃ x y : BinaryLinearThree.Vector, x 2 = 0 ∧ x ≠ 0 ∧
    ((⁅V, Lv L v⁆ : Subgroup G).subgroupOf K).map
      (Classical.choice moduleEquiv).toMonoidHom =
      (BinaryLinearThree.DoubledParabolic.splitPlane x y).toAddSubgroup.toSubgroup

theorem lv_le_of_doubled_natural
    {L V K : Subgroup G} {v : G} (d : DoubledNaturalSource L V K v)
    (hP_V : d.parabolic ≤ normalizer (V : Set G))
    (hP_L : d.parabolic ≤ normalizer (Lv L v : Set G)) : Lv L v ≤ K := by
  by_contra hLK
  obtain ⟨x, y, hx, hxn, hsplit⟩ := d.split_points
  have hfalse := Source.not_normalizes_splitPlane d.parabolic K ⁅V, Lv L v⁆
    d.parabolic_normalizes_K d.actor d.actor_surjective
    (Classical.choice d.moduleEquiv) (fun p u => d.action_equivariant p u
      (Classical.choice d.moduleEquiv)) x y hx hxn hsplit
  apply hfalse
  intro p hp
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hP_V hp),
    mem_normalizer_iff_map_conj_eq.mp (hP_L hp)]

/-- 13.6.20 packages the two source alternatives, with no quotient-cardinality
substitute for the rank condition. -/
theorem lv_le_source
    {L V K : Subgroup G} {v : G}
    (hrank_or_doubled : primeRank 3 K = 2 ∨
      Nonempty (DoubledNaturalSource L V K v))
    (hA318 : primeRank 3 K = 2 → Lv L v ≤ K)
    (hP_V : ∀ d : DoubledNaturalSource L V K v,
      d.parabolic ≤ normalizer (V : Set G))
    (hP_L : ∀ d : DoubledNaturalSource L V K v,
      d.parabolic ≤ normalizer (Lv L v : Set G)) : Lv L v ≤ K := by
  rcases hrank_or_doubled with hr | hd
  · exact hA318 hr
  · obtain ⟨d⟩ := hd
    exact lv_le_of_doubled_natural d (hP_V d) (hP_L d)

/-- Lemma 13.6.21 with the actual marked action obstruction. -/
theorem not_le_M_source
    {L M : Subgroup G} {v : G} {K : Subgroup G}
    (_hLvK : Lv L v ≤ K) (hK_Gv : K ≤ Gv v)
    (hnotact : K ≤ Mv M v → Lv L v = ⊥)
    (hLv_nontrivial : Lv L v ≠ ⊥) : ¬ K ≤ M := by
  intro hKM
  apply hLv_nontrivial
  have hKMv : K ≤ Mv M v := by
    intro x hx
    exact ⟨hKM hx, hK_Gv hx⟩
  exact le_antisymm (le_of_eq (hnotact hKMv)) bot_le

/-- A genuine small-model source case supplies its concrete marked-module
obstruction. The conclusion is not hidden in a family tag. -/
inductive SmallSourceCase (L V : Subgroup G) (v : G) (K : Subgroup G) : Prop
  | l3 (model : IsLinearTwoBlock K 3)
  | l3_doubled (model : DoubledNaturalSource L V K v)
  | sp4 (model : IsSp4FourBlock K)
  | g2 (model : CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsG2TwoBlock K)
  | ahat6 (model : IsExceptionalAhat6Block K)
  | a7 (model : IsAlternatingBlock K 7)
  | a7_exceptional (model : IsExceptionalA7Block K)

/-- The residual identity in 13.6.23(1), using the actual prime-to-three
residual of Gᵥ. -/
theorem residual_eq_source
    {v : G} {K : Subgroup G} (hK : K ≤ Gv v)
    (hnormal : (K.subgroupOf (Gv v)).Normal)
    (hperfect : IsPPerfect 3 (K.subgroupOf (Gv v)))
    (hquot : IsPGroup 3 ((Gv v) ⧸ K.subgroupOf (Gv v))) :
    K = (pResidual 3 (Gv v)).map (Gv v).subtype :=
  lemma_13_6_23_one (_L := (⊥ : Subgroup G)) (_M := (⊥ : Subgroup G))
    (_V := (⊥ : Subgroup G)) (_z := v) hK hnormal hperfect hquot

/-- The surviving rank-four branch keeps the actual isomorphism, nontrivial
Dynkin action and middle-node parabolic. -/
theorem rank_four_source {K : Subgroup G} (d : RankFourData K) :
    Nonempty (d.Kplus ⧸ pCore 2 d.Kplus ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
      (∃ t : d.T, d.dynkin_action t ≠ 1) ∧
      d.middle_parabolic < ⊤ ∧ d.middle_node = 1 :=
  ⟨d.group_equiv, d.dynkin_nontrivial, d.middle_parabolic_proper, d.middle_node_eq⟩

/-- The final orthogonal paragraph uses the prime-to-three core and the
literal equalities to all three centralizers. -/
theorem orthogonal_source
    {L M V : Subgroup G} {z v : G} {K : Subgroup G} [Finite G]
    (d : OrthogonalSixData L M V z v K)
    (T : Sylow 2 G) (hT : (T : Subgroup G) = d.T)
    (hvT : v ∈ T) (hv : v ≠ 1)
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hXnorm : (T : Subgroup G) ≤ normalizer (d.X : Set G))
    (hJ : elementaryAbelianMaxJ ((d.X ⊔ Tv (T : Subgroup G) v).pCoreIn 2) =
      elementaryAbelianMaxJ ((K ⊔ Tv (T : Subgroup G) v).pCoreIn 2))
    (h16 : ambientPCore 2 (K ⊔ d.T) = ⊥) : False :=
  have h16' : (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥ := by
    rw [← hT] at h16
    exact h16
  Source.false_of_orthogonal_thompson_comparison
    T v K d.X hvT hv d.X_le_Gv hXnorm hidx (by
      exact hJ) h16'

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
