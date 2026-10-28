module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoBinaryFive
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoFixed
public import Theory.SpecificGroups.SymplecticFour.SylowFixerThreeRank
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Cubic
public import Theory.SpecificGroups.G2.SylowFixerThreeRank
public import Theory.SpecificGroups.G2.CubicFieldActors
public import Theory.SpecificGroups.ReeF4.InvolutionCentralizerThreeRank
public import Theory.SpecificGroups.ReeF4.CubicFieldActors
public import Theory.SpecificGroups.Triality.SylowFixerThreeRank
public import Theory.SpecificGroups.Triality.CubicComponentAction
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Completing the original rank-two component exclusion

For each remaining Sp₄, G₂, genuine triality and Ree model, rank saturation
makes the original cubic actors inner. The same faithful Sylow E9 then
embeds in the fixed group of the original Sylow-fixing involution, whose
cubic rank is at most one by the intrinsic model calculation. This excludes
all four remaining families, including genuine triality at field size two.
Simplicity and perfectness are inherited from the selected source component.

The final theorem gives cubic rank one for that same selected K and action.
It retains every original point, marking, TI and nonsingular-centralizer
hypothesis. The rank-one argument on printed p.833, abelian point span,
12.6.27--34 and universal NaturalReduction remain source obligations.
Source: Aschbacher--Smith, proof of 12.6.26, printed pp.832--833.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hz hTV hTz hbound hH hn a in
/-- All nonbinary symplectic rows are excluded on the original selected component. -/
theorem SourceHypothesis.original_rank_two_not_symplectic
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) {n : ℕ} (hn2 : 2 ≤ n) :
    ¬ ClassicalGroup.IsPSp (Nonabelian.Setup.star H c.K) 2 (2^n) := by
  rintro ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let f := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_eq_of_lt (by decide : 2 = 2^1)
      (Nat.pow_lt_pow_right (by decide) (by omega))
  exact S.original_rank_two_fixed_rank_contradiction D hZ z hz hTV hTz hbound hH hn c a
    hTI hns hr f
    (Theory.SpecificGroups.SymplecticFour.OddFieldActors.cubic_primePower_actor_inner hlarge)
    (Theory.SpecificGroups.SymplecticFour.sylow_fixer_fixed_threeRank_le_one hF (by omega))


include hz hTV hTz hbound hH hn a in
/-- The actual large Ree family is excluded, inheriting the source component's simplicity. -/
theorem SourceHypothesis.original_rank_two_not_ree
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* ReeF4.Model m) := by
  rintro ⟨e⟩
  let : IsSimpleGroup (Nonabelian.Setup.star H c.K) :=
    S.original_selectedComponent_simple D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := c.component.2
  let : IsSimpleGroup (ReeF4.Model m) := e.symm.isSimpleGroup
  let : Group.IsPerfect (ReeF4.Model m) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact S.original_rank_two_fixed_rank_contradiction D hZ z hz hTV hTz hbound hH hn c a
    hTI hns hr e (ReeF4.CubicFieldActors.cubic_primePower_actor_inner hm)
    (fun _ α hα _ => ReeF4.involution_fixed_threeRank_le_one hm α hα)

include hz hTV hTz hbound hH hn a in
/-- Every remaining even split G2 row is excluded on the original marked component. -/
theorem SourceHypothesis.original_rank_two_not_splitGTwo
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) {n : ℕ} (hn2 : 2 ≤ n) :
    ¬ ClassificationModels.IsG2At (Nonabelian.Setup.star H c.K) (2^n) := by
  rintro ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_eq_of_lt (by decide : 2 = 2^1)
      (Nat.pow_lt_pow_right (by decide) (by omega))
  exact S.original_rank_two_fixed_rank_contradiction D hZ z hz hTV hTz hbound hH hn c a
    hTI hns hr e (Atlas.G2.CubicFieldActors.cubic_primePower_actor_inner hlarge)
    (Atlas.G2.sylow_fixer_fixed_threeRank_le_one hlarge)

include hz hTV hTz hbound hH hn a in
/-- Only genuine triality remains in the original rank-two branch, retaining
condition (*) on the exact centralizer and both intrinsic quotient cores. -/
theorem SourceHypothesis.original_rank_two_triality_model
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    let B := Nonabelian.Setup.star H c.K
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let C := centralizer (U : Set a.action.range)
    2 ≤ primeRank 3 (pCore 3 (C ⧸ pCore 2 C)) ∧
      ∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2^n) B := by
  obtain ⟨hcore,hmodels⟩ := S.original_rank_two_nonlinear_models D hZ z hz hTV hTz
    hbound hH hn c a hTI hns hr
  refine ⟨hcore,?_⟩
  rcases hmodels with ⟨n,hn2,h⟩ | ⟨n,hn2,h⟩ | h | ⟨m,hm,h⟩
  · exact (S.original_rank_two_not_symplectic D hZ z hz hTV hTz hbound hH hn c a hTI hns hr hn2 h).elim
  · exact (S.original_rank_two_not_splitGTwo D hZ z hz hTV hTz hbound hH hn c a hTI hns hr hn2 h).elim
  · exact h
  · exact (S.original_rank_two_not_ree D hZ z hz hTV hTz hbound hH hn c a hTI hns hr hm h).elim


include hz hTV hTz hbound hH hn a in
/-- The genuine graph-field triality row is excluded at every positive binary exponent. -/
theorem SourceHypothesis.original_rank_two_not_triality
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) {n : ℕ} (hn0 : 1 ≤ n) :
    ¬ Triality.Standard.IsTrialityGroupAt (2^n) (Nonabelian.Setup.star H c.K) := by
  intro hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn0).mp hm
  let : IsSimpleGroup (Nonabelian.Setup.star H c.K) :=
    S.original_selectedComponent_simple D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := c.component.2
  let : IsSimpleGroup (Triality.Standard.BinaryCarrier n hn0) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Triality.Standard.BinaryCarrier n hn0) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact S.original_rank_two_fixed_rank_contradiction D hZ z hz hTV hTz hbound hH hn c a
    hTI hns hr e
    (fun A hA hr b hb ⟨k,hk⟩ =>
      Triality.Standard.CubicComponentAction.primePower_actor_inner n hn0 A hA hr b hb k hk)
    (Triality.Standard.sylow_fixer_fixed_threeRank_le_one n hn0)

include hz hTV hTz hbound hH hn a in
/-- The complete original rank-two branch is impossible, on the same selected component and action. -/
theorem SourceHypothesis.original_selectedComponent_not_rank_two
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    primeRank 3 c.K ≠ 2 := by
  intro hr
  obtain ⟨_,n,hn0,hm⟩ := S.original_rank_two_triality_model D hZ z hz hTV hTz
    hbound hH hn c a hTI hns hr
  exact S.original_rank_two_not_triality D hZ z hz hTV hTz hbound hH hn c a hTI hns hr hn0 hm

include hz hTV hTz hbound hH hn a in
/-- After the full Theorem C inspection, the original selected component has cubic rank one. -/
theorem SourceHypothesis.original_selectedComponent_rank_one
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    primeRank 3 c.K = 1 := by
  rcases S.original_selectedComponent_three_rank D hZ z hz hTV hTz hbound hns hH hn c with h|h
  · exact h
  · exact (S.original_selectedComponent_not_rank_two D hZ z hz hTV hTz hbound hH hn c a hTI hns h).elim


end CFSG.Quasithin.Chapter12.Section06
