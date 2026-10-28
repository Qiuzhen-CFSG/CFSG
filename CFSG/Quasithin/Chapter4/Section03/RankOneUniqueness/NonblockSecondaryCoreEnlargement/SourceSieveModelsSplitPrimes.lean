module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsTwoCore
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.EvenRankTwo

/-!
This additive source variant uses `SecondaryActionData` and preserves the
full quotient and central-cover hypotheses without universal radical movement.

# Common split primes in the nonblock Lie-model sieve

The ambient two-core reduction carries the genuine outside source actor to
an ordinary component. The proved binary PSL₃ and PSp₄ split-prime residual
theorems then exclude common primes, with only the diagonal cubic possibility
remaining for PSL₃. In that possibility the reduced ambient theta group,
modulo its own prime-to-three core, has an actual PGL₃ model.

The source torus exponent n and model field exponent f remain distinct.
The PGL conclusion names the reduced theta quotient explicitly; it does not
silently identify it with the original component action or prime-core quotient.
The remaining model restrictions and source assembly are owned by
qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith A.3.18, pp.51–53; original 4.3.12(2), p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open ChapterA.Section03.OddPrime.SourceModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- A noncubic prime shared by the source torus and a binary linear split
torus excludes that full component model. -/
theorem SecondaryActionData.not_binary_linear_of_common_noncubic_prime (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 < f)
    (hd : p ∣ 2 ^ n - 1) (hdf : p ∣ 2 ^ f - 1) :
    ¬ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2 ^ f) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hz := SecondaryActionData.twoCoreComponent_center_eq_bot s e (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F))
  have hZ : IsPGroup 2 (center (SecondaryActionData.twoCoreComponent s)) := by
    rw [hz]
    exact IsPGroup.of_subsingleton 2 _
  have hr := linear_component_eq_primeClosure_and_residual
    (SecondaryActionData.twoCoreRoot_sqtk s D h) (SecondaryActionData.twoCoreComponent_isComponent s)
    hZ hf hp hp3 hF hdf (SecondaryActionData.twoCoreCentralModel s e (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)))
  exact (SecondaryActionData.twoCoreComponent_ne_prime_closures s hp ho hd).2 hr.2

/-- Any common odd prime in these two actual tori is the diagonal prime three. -/
theorem SecondaryActionData.binary_linear_common_prime_eq_three (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hf : 1 < f)
    (hd : p ∣ 2 ^ n - 1) (hdf : p ∣ 2 ^ f - 1)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) : p = 3 := by
  by_contra hp3
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hlarge : 3 < p := by have hh := hp.two_le; omega
  exact SecondaryActionData.not_binary_linear_of_common_noncubic_prime s D h hp hlarge hf hd hdf hm

/-- No odd prime can be shared by the source torus and a binary symplectic
split torus. The original C-component, rather than a central cover of it,
is carried through the ordinary-component reduction. -/
theorem SecondaryActionData.not_symplectic_of_common_prime (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hf : 1 < f)
    (hd : p ∣ 2 ^ n - 1) (hdf : p ∣ 2 ^ f - 1) :
    ¬ ClassicalGroup.IsPSp (s.component ⧸ pCore 2 s.component) 2 (2 ^ f) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  have hz := SecondaryActionData.twoCoreComponent_center_eq_bot s a
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
  have hZ : IsPGroup 2 (center (SecondaryActionData.twoCoreComponent s)) := by
    rw [hz]
    exact IsPGroup.of_subsingleton 2 _
  have hr := SymplecticResidual.component_eq_primeClosure_and_residual
    (SecondaryActionData.twoCoreRoot_sqtk s D h) (SecondaryActionData.twoCoreComponent_isComponent s)
    hZ hf hp ho hF hdf (SecondaryActionData.twoCoreCentralModel s a
      Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot)
  exact (SecondaryActionData.twoCoreComponent_ne_prime_closures s hp ho hd).2 hr.2

/-- The remaining common cubic prime yields an actual PGL₃ model of the
reduced ambient theta quotient. Its core is that of theta itself. -/
theorem SecondaryActionData.binary_linear_reduced_theta_isPGL (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {f : ℕ} (hf : 1 < f) (hd : 3 ∣ 2 ^ n - 1) (hdf : 3 ∣ 2 ^ f - 1)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) :
    IsPGLThree ((theta (rootNormalizer c ⧸ pCore 2 (rootNormalizer c))) ⧸
      pPrimeCore 3 (theta (rootNormalizer c ⧸ pCore 2 (rootNormalizer c)))) (2 ^ f) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hz := SecondaryActionData.twoCoreComponent_center_eq_bot s e (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F))
  have hZ : IsPGroup 2 (center (SecondaryActionData.twoCoreComponent s)) := by
    rw [hz]
    exact IsPGroup.of_subsingleton 2 _
  rcases CubicLinearAction.theta_eq_or_isPGLThree
    (SecondaryActionData.twoCoreRoot_sqtk s D h) (SecondaryActionData.twoCoreComponent_isComponent s)
    hZ (by omega : 0 < f) hF hdf
    (SecondaryActionData.twoCoreCentralModel s e (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F))) with ht | ht
  · exact ((SecondaryActionData.twoCoreComponent_ne_prime_closures s Nat.prime_three
      (by decide) hd).1 ht).elim
  · exact ht

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
