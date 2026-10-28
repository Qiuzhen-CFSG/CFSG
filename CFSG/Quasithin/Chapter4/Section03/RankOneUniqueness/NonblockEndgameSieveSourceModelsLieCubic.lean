module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceModelsTwoCore
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SymplecticCubicResidual
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ReeCubicResidual
public import Theory.SpecificGroups.Triality.CubicComponentAction
public import Theory.SpecificGroups.Triality.BinaryCenter

/-!
This additive source variant uses `SecondarySourceData` and preserves the
full quotient and central-cover hypotheses without universal radical movement.

# Cubic Lie-family exclusions in the nonblock sieve

An order-three element of the source torus remains outside the ordinary
component in the ambient two-core quotient. The concrete symplectic, G₂,
triality and Ree cubic-field calculations put every such element inside
that component, a contradiction. The triality argument uses the genuine
binary graph-field carrier, including its smallest field. The Ree argument
uses the centerless branch already supplied by the full quotient catalogue.

These are actual applications of the ordinary-component results to the
literal nonblock C-component. Their final dispatch and the other model
restrictions remain with qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith A.3.18, pp.51–53, and original 4.3.12–16, pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels ChapterA.Section03.OddPrime.SourceModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- A cubic source torus excludes every genuine binary PSp₄ row. -/
theorem SecondarySourceData.not_symplectic_of_three_dvd (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) {f : ℕ} (hf : 2 ≤ f) :
    ¬ ClassicalGroup.IsPSp (s.component ⧸ pCore 2 s.component) 2 (2 ^ f) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  have hz := SecondarySourceData.twoCoreComponent_center_eq_bot s a
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
  have hZ : IsPGroup 2 (center (SecondarySourceData.twoCoreComponent s)) := by
    rw [hz]
    exact IsPGroup.of_subsingleton 2 _
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega : 1 < f)
  have hr := SymplecticCubicResidual.component_eq_primeClosure_and_residual
    (SecondarySourceData.twoCoreRoot_sqtk s D h) (SecondarySourceData.twoCoreComponent_isComponent s)
    hZ hlarge (SecondarySourceData.twoCoreCentralModel s a
      Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot)
  exact (SecondarySourceData.twoCoreComponent_ne_prime_closures s Nat.prime_three (by decide) hd).2 hr.2

/-- A cubic source torus excludes every genuine binary G₂ row. -/
theorem SecondarySourceData.not_g2_of_three_dvd (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) {f : ℕ} (hf : 2 ≤ f) :
    ¬ ClassificationModels.IsG2At (s.component ⧸ pCore 2 s.component) (2 ^ f) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega : 1 < f)
  have hz := SecondarySourceData.twoCoreComponent_center_eq_bot s e
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hlarge)
  have hZ : IsPGroup 2 (center (SecondarySourceData.twoCoreComponent s)) := by
    rw [hz]
    exact IsPGroup.of_subsingleton 2 _
  have hr := G2CubicResidual.component_eq_primeClosure_and_residual
    (SecondarySourceData.twoCoreRoot_sqtk s D h) (SecondarySourceData.twoCoreComponent_isComponent s)
    hZ hlarge (SecondarySourceData.twoCoreCentralModel s e
      (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hlarge))
  exact (SecondarySourceData.twoCoreComponent_ne_prime_closures s Nat.prime_three (by decide) hd).2 hr.2

/-- The genuine triality carrier, including ³D₄(2), is excluded by a cubic torus. -/
theorem SecondarySourceData.not_triality_of_three_dvd (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) {f : ℕ} (hf : 1 ≤ f) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ f) (s.component ⧸ pCore 2 s.component) := by
  intro hm
  have hf0 : 0 < f := by omega
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f hf0).mp hm
  have hz := SecondarySourceData.twoCoreComponent_center_eq_bot s e
    (Triality.Standard.binaryCarrier_center_eq_bot f hf0)
  have hZ : Nat.Coprime 3 (Nat.card (center (SecondarySourceData.twoCoreComponent s))) := by
    rw [hz]
    simp
  have hr := Triality.Standard.CubicComponentAction.component_eq_primeClosure_and_residual
    ((SecondarySourceData.twoCoreRoot_sqtk s D h).stronglyQuasithin 3 Nat.prime_three (by decide))
    (SecondarySourceData.twoCoreComponent_isComponent s) hZ f hf0
    (SecondarySourceData.twoCoreCentralModel s e (Triality.Standard.binaryCarrier_center_eq_bot f hf0))
  exact (SecondarySourceData.twoCoreComponent_ne_prime_closures s Nat.prime_three (by decide) hd).2 hr.2

/-- The centerless Ree branch of the full quotient catalogue is excluded by
its actual cubic torus actor. -/
theorem SecondarySourceData.not_ree_of_three_dvd_of_center_bot (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) (hz : center (s.component ⧸ pCore 2 s.component) = ⊥)
    {m : ℕ} (hm : 1 ≤ m) :
    ¬ IsReeF4At (s.component ⧸ pCore 2 s.component) m := by
  rintro ⟨d, ⟨a⟩⟩
  let e := a.trans d.modelEquiv
  have hzI := SecondarySourceData.twoCoreComponent_center_eq_bot s (MulEquiv.refl _) hz
  have hZ : IsPGroup 2 (center (SecondarySourceData.twoCoreComponent s)) := by
    rw [hzI]
    exact IsPGroup.of_subsingleton 2 _
  let j := (SecondarySourceData.twoCoreCentralModel s (MulEquiv.refl _) hz).trans e
  have hr := ReeCubicResidual.component_eq_primeClosure_and_residual
    (SecondarySourceData.twoCoreRoot_sqtk s D h) (SecondarySourceData.twoCoreComponent_isComponent s) hZ hm j
  exact (SecondarySourceData.twoCoreComponent_ne_prime_closures s Nat.prime_three (by decide) hd).2 hr.2

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
