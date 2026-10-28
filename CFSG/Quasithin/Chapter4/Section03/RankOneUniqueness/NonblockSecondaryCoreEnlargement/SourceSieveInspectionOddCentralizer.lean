module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionCubicSylows
public import Theory.SpecificGroups.OddThreeCyclicCentralizers
public import Theory.SpecificGroups.PSL3.OddMovedTwoGroups
public import Theory.SpecificGroups.SU3.MovedTwoGroups
public import Theory.GroupAction.CyclicTwoMovement

/-!
# Excluding the odd ternary rows on the actual source action

The secondary two-core is central in an odd ternary model. Mutual
normalization and perfectness then make the radical image centralize the
secondary image. Whole-radical generation identifies that radical with
the moved core; this movement is derived only after the model-specific
centrality calculation, with the original normalQuotientAction unchanged.

Moved two-subgroups of the odd-prime ternary automorphism groups are inner.
Inside the model, a two-subgroup centralizing a nontrivial perfect subgroup
is cyclic: choose a central involution and use its actual GL₂/GU₂ cubic
central quotient. An odd torus cannot move a nontrivial cyclic two-group.
This contradicts the original nontrivial radical action.

The model is initially the inner image. The already proved degree-two and
cubic centerlessness clauses recover the full component quotient before
transporting automorphisms. The final export removes all odd ternary rows
from the source frontier and is consumed by NonblockSecondaryCoreEnlargement.SourceSieveAssembly;
binary rank-two models and the degree-five J₄ row remain.
Source: Aschbacher--Smith A.3.21(a), p.55, and 4.3.12--16, pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- Generation and core movement put the odd ternary radical image inside the inner image. -/
theorem SecondaryActionData.odd_ternary_radical_le_inner
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
      ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p) :
    SecondaryActionData.radicalImage s ≤ SecondaryActionData.componentImage s := by
  let := s.normal
  let := s.quasisimple
  have hdegree := SecondaryActionData.odd_ternary_degree_eq_two s hn hp ho hm
  have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h
    (by rw [hdegree]; decide)
  let a : (s.component ⧸ pCore 2 s.component) ≃* SecondaryActionData.componentImage s :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
      (SecondaryActionData.sieveCentralQuotientEquiv s)
  let : IsSimpleGroup (s.component ⧸ pCore 2 s.component) := by
    let : IsSimpleGroup ((s.component ⧸ pCore 2 s.component) ⧸ center
      (s.component ⧸ pCore 2 s.component)) := IsQuasisimple.simple
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  let R := SecondaryActionData.radicalImage s
  let Y := SecondaryActionData.torusImage s
  have hr : IsPGroup 2 R := (SourceImages.radical_geometry c s.component s.radical_normalizer).1
  have he := (SecondaryActionData.odd_ternary_action_structure s hn hg hp ho hm).2.2.2.1
  have hmoved : ⁅R,Y⁆ = R := by
    change ⁅SecondaryActionData.radicalImage s,SecondaryActionData.torusImage s⁆ =
      SecondaryActionData.radicalImage s
    rw [he]
    exact SecondaryActionData.coreImage_moved s
  rw [SecondaryActionData.componentImage_eq_inner]
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,hconj,⟨e⟩⟩
  · let k := MulAut.congr (a.trans e)
    let : IsSimpleGroup PSL(3,F) := (a.trans e).symm.isSimpleGroup
    let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective
      (f := (a.trans e).toMonoidHom) (a.trans e).surjective
    have hi := Matrix.PSL3.OddInvolutionFixed.moved_twoGroup_le_inner
      (Group.IsPerfect.not_isSolvable PSL(3,F)) hp ho hF
      (R.map k.toMonoidHom) (Y.map k.toMonoidHom) (hr.map k.toMonoidHom)
      (by rw [←map_commutator,hmoved])
    rw [←MulAut.map_innerSubgroup_congr (a.trans e)] at hi
    intro r hr
    obtain ⟨b,hb,hbr⟩ := hi (mem_map_of_mem k.toMonoidHom hr)
    exact k.injective hbr ▸ hb
  · let k := MulAut.congr (a.trans e)
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      (a.trans e).symm.isSimpleGroup
    let : Fact p.Prime := ⟨hp⟩
    have hfixed : Nat.card {z : F // J.conj z=z} = p := by
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1
        (by decide) (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hconj)
    have hi := BenderSuzuki.MatrixGroups.HermitianForm.PrimeTwoActors.moved_twoGroup_le_inner_of_prime
      J hp ho hF hfixed (R.map k.toMonoidHom) (Y.map k.toMonoidHom) (hr.map k.toMonoidHom)
      (by rw [←map_commutator,hmoved])
    rw [←MulAut.map_innerSubgroup_congr (a.trans e)] at hi
    intro r hr
    obtain ⟨b,hb,hbr⟩ := hi (mem_map_of_mem k.toMonoidHom hr)
    exact k.injective hbr ▸ hb

private theorem cyclic_centralizing_of_equiv
    {A M : Type*} [Group A] [Group M] (e : A ≃* M)
    (hc : ∀ (B R : Subgroup M), Group.IsPerfect B → B ≠ ⊥ → IsPGroup 2 R →
      R ≤ centralizer (B : Set M) → IsCyclic R)
    (B R : Subgroup A) [Group.IsPerfect B] (hB : B ≠ ⊥)
    (hR : IsPGroup 2 R) (hRB : R ≤ centralizer (B : Set A)) : IsCyclic R := by
  let b := e.subgroupMap B
  let r := e.subgroupMap R
  let : Group.IsPerfect (B.map e.toMonoidHom) := Group.IsPerfect.ofSurjective
    (f := b.toMonoidHom) b.surjective
  let hcyc : IsCyclic (R.map e.toMonoidHom) :=
    hc (B.map e.toMonoidHom) (R.map e.toMonoidHom) inferInstance
    (fun hh => hB ((B.map_eq_bot_iff_of_injective e.injective).mp hh))
    (hR.map e.toMonoidHom)
    ((map_mono hRB).trans (map_centralizer_le_centralizer_image B e.toMonoidHom))
  exact @isCyclic_of_injective R (R.map e.toMonoidHom) _ _ hcyc r.toMonoidHom r.injective

/-- The actual radical image is cyclic because it centralizes the perfect secondary image. -/
theorem SecondaryActionData.odd_ternary_radical_isCyclic
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
      ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p) :
    IsCyclic (SecondaryActionData.radicalImage s) := by
  let := s.normal
  let X := SecondaryActionData.secondaryImage s
  let R := SecondaryActionData.radicalImage s
  let I := SecondaryActionData.componentImage s
  have hRI := SecondaryActionData.odd_ternary_radical_le_inner s hn hg D h hp ho hm
  have hXI := SecondaryActionData.secondaryImage_le_componentImage s
  let B := X.subgroupOf I
  let Q := R.subgroupOf I
  let b := subgroupOfEquivOfLe hXI
  let r := subgroupOfEquivOfLe hRI
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  let : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot _).mpr
    (SourceImages.secondaryImage_ne_bot c s.component s.secondary_le s.secondary_model)
  let : Nontrivial B := b.nontrivial
  have hB : B ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot B).mp inferInstance
  have hQ : IsPGroup 2 Q :=
    (SourceImages.radical_geometry c s.component s.radical_normalizer).1.of_equiv r.symm
  have hQB : Q ≤ centralizer (B : Set I) := by
    intro q hq x hx
    exact Subtype.ext ((SecondaryActionData.odd_ternary_action_structure s hn hg hp ho hm).2.2.1
      hq x hx)
  have hcyc : IsCyclic Q := by
    rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,hconj,⟨e⟩⟩
    · apply cyclic_centralizing_of_equiv e (fun P A hP hne hA hAP => ?_) B Q hB hQ hQB
      let := hP
      exact Theory.SpecificGroups.OddThreeLevi.linear_twoGroup_centralizing_perfect_isCyclic
        (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho (k := 1)
          (by simpa using hF)) P A hne hA hAP
    · apply cyclic_centralizing_of_equiv e (fun P A hP hne hA hAP => ?_) B Q hB hQ hQB
      let := hP
      exact Theory.SpecificGroups.OddThreeLevi.unitary_twoGroup_centralizing_perfect_isCyclic
        J hp ho hF hconj P A hne hA hAP
  let := hcyc
  exact isCyclic_of_injective r.symm.toMonoidHom r.symm.injective

/-- Odd torus movement excludes every odd-prime ternary inner model. -/
theorem SecondaryActionData.not_odd_ternary_inner_of_generation
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
      ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p) : False := by
  let := s.normal
  let := SecondaryActionData.odd_ternary_radical_isCyclic s hn hg D h hp ho hm
  have hdegree := SecondaryActionData.odd_ternary_degree_eq_two s hn hp ho hm
  have he := (SecondaryActionData.odd_ternary_action_structure s hn hg hp ho hm).2.2.2.1
  apply s.radical_action
  apply cyclic_twoGroup_eq_bot_of_odd_movement (SecondaryActionData.radicalImage s)
    (SecondaryActionData.torusImage s)
    (SourceImages.radical_geometry c s.component s.radical_normalizer).1
  · have hd := (s.torus.subgroupOf (rootNormalizer c)).card_map_dvd s.action
    rw [Nat.card_congr (subgroupOfEquivOfLe s.torus_le).toEquiv,s.torus_card] at hd
    have hodd : Odd (2^n-1) := by rw [hdegree]; decide
    exact hodd.of_dvd_nat hd
  · exact SourceImages.image_normalizes c s.component s.torus_normalizes_radical
  · rw [he]
    exact SecondaryActionData.coreImage_moved s

/-- The odd-characteristic rows are excluded by the actual moved radical.
Only binary rank-two models and the degree-five J₄ row remain. -/
theorem SecondaryActionData.inspection_remaining_rows_after_odd_ternary
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
      (SecondaryActionData.componentImage s) f) ∨
      (n=5 ∧ Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model)) := by
  rcases SecondaryActionData.inspection_remaining_rows_after_sporadic_exponent s hn hg D h
    with ⟨rfl,p,hp,ho,hm⟩ | hm | hm
  · have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h (by decide)
    let a : (s.component ⧸ pCore 2 s.component) ≃* SecondaryActionData.componentImage s :=
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
        (SecondaryActionData.sieveCentralQuotientEquiv s)
    exact (SecondaryActionData.not_odd_ternary_inner_of_generation s hn hg D h hp ho
      (hm.elim (fun h => Or.inl (h.of_mulEquiv a.symm))
        (fun h => Or.inr (h.of_mulEquiv a.symm)))).elim
  · exact Or.inl hm
  · exact Or.inr hm
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
