module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceInspectionG2
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectLocalDegrees
public import Theory.SpecificGroups.PSL3.MovedTwoGroups
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry

/-!
# The source degree in the remaining binary PSL₃ row

Core movement removes the diagonal, field and graph contributions of the
core image; whole-radical generation then puts the radical inside the inner
component. Its nontrivial two-group normalizer is conjugate into a point or
line parabolic. The actual secondary section order forces n to divide the
model degree f, so every prime of 2ⁿ − 1 is a split torus prime in PSL₃.
Each noncubic such prime contradicts the source rank-one restriction.
Consequently n = 2 and f is even. The source center calculation then lifts
the inner marking to the full two-core quotient.

The remaining step f = 2 needs the actual normalizer-control clause; this
module neither assumes it implies full Sylow normalization nor asserts that
the embedded rank-one section is already the whole Levi factor.
Source: Aschbacher--Smith 4.3.12--16, printed pp.617--618.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}
/-- Core movement and generation put the literal radical image inside the
actual projective linear component. -/
theorem SecondarySourceData.binary_linear_radical_le_inner (s : SecondarySourceData c n)
    (hg : SecondarySourceData.ActionGeneration s) {f : ℕ} (hf : 2≤f)
    (hm : ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) 3 (2^f)) :
    SecondarySourceData.radicalImage s ≤ SecondarySourceData.componentImage s := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := s.normal
  let := s.quasisimple
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := (SecondarySourceData.centralQuotientEquiv s).trans e
  let k := MulAut.centralQuotientAction a
  have hi : SecondarySourceData.coreImage s ≤ SecondarySourceData.componentImage s := by
    rw [SecondarySourceData.componentImage_eq_inner]
    have hmoved : ⁅(SecondarySourceData.coreImage s).map k,
        (SecondarySourceData.torusImage s).map k⁆ = (SecondarySourceData.coreImage s).map k := by
      rw [←map_commutator,SecondarySourceData.coreImage_moved]
    have hp := (SourceImages.radical_geometry c s.component s.radical_normalizer).1
    have hQ : IsPGroup 2 (SecondarySourceData.coreImage s) :=
      hp.to_le (SourceImages.radical_geometry c s.component s.radical_normalizer).2.1
    have hh := Matrix.PSL3.MovedTwoGroups.moved_twoGroup_le_inner_of_coverage
      (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hF)
      _ _ (hQ.map k) hmoved
    intro x hx
    obtain ⟨y,hy⟩ := hh (mem_map_of_mem k hx)
    obtain ⟨z,hz⟩ := (MulAut.centralQuotientAction_inner_iff a x).mp ⟨y,hy.symm⟩
    exact ⟨z,hz.symm⟩
  rw [←hg]
  apply sup_le hi
  rw [SecondarySourceData.componentImage_eq_inner]
  exact (Subgroup.commutator_mono le_top
    (by rw [←SecondarySourceData.componentImage_eq_inner]
        exact SecondarySourceData.secondaryImage_le_componentImage s)).trans
    (Subgroup.commutator_le_right _ _)

/-- The secondary section in the actual proper two-local forces divisibility
of the original source degree into the binary model degree. -/
theorem SecondarySourceData.binary_linear_degree_dvd (s : SecondarySourceData c n)
    (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    {f : ℕ} (hf : 2≤f)
    (hm : ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) 3 (2^f)) : n ∣ f := by
  have hRI := SecondarySourceData.binary_linear_radical_le_inner s hg hf hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := s.normal
  let := s.quasisimple
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hXI := SecondarySourceData.secondaryImage_le_componentImage s
  let I := SecondarySourceData.componentImage s
  let X := SecondarySourceData.secondaryImage s
  let R := SecondarySourceData.radicalImage s
  let b := subgroupOfEquivOfLe hXI
  let r := subgroupOfEquivOfLe hRI
  let B := (X.subgroupOf I).map e.toMonoidHom
  let W := (R.subgroupOf I).map e.toMonoidHom
  let b' := b.symm.trans ((X.subgroupOf I).equivMapOfInjective e.toMonoidHom e.injective)
  let r' := r.symm.trans ((R.subgroupOf I).equivMapOfInjective e.toMonoidHom e.injective)
  have hW : W≠⊥ := by
    intro hh
    have hcard : Nat.card R=1 := (Nat.card_congr r'.toEquiv).trans (by change Nat.card W=1; rw [hh]; simp)
    exact s.radical_action (R.eq_bot_of_card_eq hcard)
  have hpW : IsPGroup 2 W :=
    ((SourceImages.radical_geometry c s.component s.radical_normalizer).1).of_equiv r'
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f:=b'.toMonoidHom) b'.surjective
  have hBW : B ≤ normalizer (W : Set (PSL(3,F))) := by
    apply le_trans (map_mono ?_) ((R.subgroupOf I).le_normalizer_map e.toMonoidHom)
    intro x hx y
    exact (SourceImages.radical_geometry c s.component s.radical_normalizer).2.2.2.1 hx y.val
  obtain ⟨g,point,hgl⟩ := CFSG.Quasithin.MainConverse.LinearThreeGeometry.twoLocal_conjugate_le
    F (by omega : 0<f) hF (normalizer (W : Set _)) ⟨W,hW,hpW,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp B.subtype
  have hj : Function.Injective j := (MulAut.conj g).injective.comp B.subtype_injective
  have hjN : j.range ≤ (normalizer (W : Set _)).map (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨x,rfl⟩
    exact mem_map_of_mem _ (hBW x.property)
  have hdB : (2^n)^2-1 ∣ Nat.card B := by
    rw [←Nat.card_congr b'.toEquiv]
    have hmodel : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^n) :=
      SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
    obtain ⟨K,_,_,hK,⟨a⟩⟩ := hmodel
    have hc := card_quotient_dvd_card (pCore 2 X)
    let : CharP K 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hK
    rw [Nat.card_congr (a.trans (Theory.PSL2.sl2QuotientEquiv K).symm).toEquiv,
      Atlas.card_sl_two,hK] at hc
    exact (dvd_mul_left _ _).trans hc
  apply Matrix.PSL3.LinearThree.PerfectSubgroups.degree_dvd_of_perfect_parabolic
    hF hf (by omega) hdB j hj
  cases point
  · exact Or.inr (hjN.trans hgl)
  · exact Or.inl (hjN.trans hgl)

/-- Every source torus prime is split in the model. The noncubic rank-one
restriction therefore forces the original source degree to be two. -/
theorem SecondarySourceData.binary_linear_source_degree_two (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    {f : ℕ} (hf : 2≤f)
    (hm : ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) 3 (2^f)) : n=2 := by
  have hnf := SecondarySourceData.binary_linear_degree_dvd s hn hg hf hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := s.quasisimple
  apply Nat.BinarySignedTorus.exponent_eq_two_of_prime_dvd_eq_three hn
  intro p hp hd
  by_contra hp3
  let : Fact p.Prime := ⟨hp⟩
  have ho := Nat.BinarySignedTorus.odd_of_dvd_sub (by omega : 0<n) hd
  have hdF : p ∣ Nat.card F-1 := by
    rw [hF]
    exact hd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)
  have hrI : 2≤primeRank p (SecondarySourceData.componentImage s) := by
    rw [primeRank_congr p e]
    exact Matrix.PSL3.SplitPrimeRank.projective_rank F hp3 hdF
  have hr : primeRank p s.component=primeRank p (SecondarySourceData.componentImage s) := by
    rw [←primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup]
    let a := SecondarySourceData.centralQuotientEquiv s
    rw [←primeRank_congr p a]
    apply primeRank_eq_of_surjective_of_coprime p (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
    rw [QuotientGroup.ker_mk']
    exact SecondarySourceData.componentQuotient_center_coprime s D h hp hp3
  have hu := SecondarySourceData.noncubic_prime_rank_one s D h hn hp ho hd hp3
  omega
/-- In the remaining binary linear row the source degree is two, the model
degree is even, and the actual full two-core quotient has this same model. -/
theorem SecondarySourceData.binary_linear_degree_two_full_model (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    {f : ℕ} (hf : 2≤f)
    (hm : ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) 3 (2^f)) :
    n=2 ∧ Even f ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2^f) := by
  have hn2 := SecondarySourceData.binary_linear_source_degree_two s D h hn hg hf hm
  have hd := SecondarySourceData.binary_linear_degree_dvd s hn hg hf hm
  have he : Even f := even_iff_two_dvd.mpr (hn2 ▸ hd)
  have hz := SecondarySourceData.componentQuotient_center_eq_bot_of_three_dvd s D h
    (by rw [hn2]; decide : 3∣2^n-1)
  let a : (s.component ⧸ pCore 2 s.component) ≃* SecondarySourceData.componentImage s :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans
        (SecondarySourceData.centralQuotientEquiv s))
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact ⟨hn2,he,F,inferInstance,inferInstance,hF,⟨a.trans e⟩⟩

/-- The proper-local order and source prime-rank arguments leave degree-two
binary linear full quotients and degree-five J₄. The linear field degree
still requires the normalizer-control argument. -/
theorem SecondarySourceData.inspection_remaining_rows_after_linear_degree
    (s : SecondarySourceData c n) (hn : 1<n)
    (hg : SecondarySourceData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (n=2 ∧ ∃ f : ℕ, 2≤f ∧ Even f ∧
      ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2^f)) ∨
      (n=5 ∧ Nonempty (SecondarySourceData.componentImage s ≃* Janko4.Model)) := by
  rcases SecondarySourceData.inspection_remaining_rows_after_g2 s hn hg D h with
    ⟨f,hf,hm⟩ | hh
  · obtain ⟨hn2,he,hm'⟩ :=
      SecondarySourceData.binary_linear_degree_two_full_model s D h hn hg hf hm
    exact Or.inl ⟨hn2,f,hf,he,hm'⟩
  · exact Or.inr hh

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
