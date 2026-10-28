module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.CubicLinearAction.ThetaQuotient
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SymplecticResidual
public import Theory.SpecificGroups.PSL3.SplitPrimeActors
public import Theory.SpecificGroups.PSL3.SplitPrimeRank

/-!
# The source A.3.18 dichotomy for binary rank-two components

Let H be SQTK and L an ordinary component with central two-kernel whose
central quotient is PSL₃(2ⁿ) or PSp₄(2ⁿ), n > 1. For every odd prime p
dividing 2ⁿ − 1, the actual component equals the source theta-p subgroup,
except possibly at p = 3 in the linear family. In that exception theta(H)
modulo its own prime-to-three core is the actual PGL₃(2ⁿ).

The cubic linear branch uses the complete fixed-nine exclusion and retains
the marked theta quotient map. In the other branches the actual split torus,
standard automorphism coverage and fixed-field rank calculation exclude outer
p-elements. Rank and the p-prime center derive component normality and the
coprime action kernel, after which prime generation recovers L itself.

This is the specialized A.3.18 statement used on N_G(Dˣ) in 2.5.7, printed
p.556 of Aschbacher–Smith. It does not change or assume the wider LemmaA318
catalogue. The earlier 2.5.6 component-placement theorem remains separate.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
variable {H : Type*} [Group H] [Finite H]

/-- Away from three, the original binary linear component is generated both
by order-p elements and by all p-elements of the ambient source group. -/
theorem linear_component_eq_primeClosure_and_residual
    {F : Type*} [Field F] [Finite F]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {L : Subgroup H} (hL : IsComponent H L) (hZ : IsPGroup 2 (center L))
    {n p : ℕ} (hn : 1 < n) (hp : p.Prime) (hp3 : 3 < p)
    (hF : Nat.card F = 2 ^ n) (hd : p ∣ 2 ^ n - 1)
    (e : L ⧸ center L ≃* PSL(3,F)) :
    L = closure {x : H | orderOf x = p} ∧ L = primeToResidual p H := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let := hL.2
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hz : Nat.Coprime p (Nat.card (center L)) := by
    obtain ⟨m, hm⟩ := hZ.exists_card_eq
    rw [hm]
    exact (Nat.coprime_two_right.mpr ho).pow_right m
  have hdF : p ∣ Nat.card F - 1 := hF ▸ hd
  have hr := Matrix.PSL3.SplitPrimeRank.component_rank F L hz e (by omega) hdF
  have hbound := hH.stronglyQuasithin p hp ho
  apply component_eq_primeClosure_and_residual hL hz hr hbound e
  intro a ha m hm
  exact Matrix.PSL3.SplitPrimeActors.inner_of_primePower (by omega) hF hp3 hdF
    (action L e).range (inner_le_range L e) (range_rank_le_two L e hz hr hbound)
    a ha ⟨m, hm⟩

/-- The noncubic linear branch uses the exact original central quotient model. -/
theorem linear_component_eq_primeToResidual_of_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {L : Subgroup H} (hL : IsComponent H L) (hZ : IsPGroup 2 (center L))
    {n p : ℕ} (hn : 1 < n) (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ 2 ^ n - 1)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n)) :
    L = primeToResidual p H := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  exact (linear_component_eq_primeClosure_and_residual hH hL hZ hn hp hp3 hF hd e).2

/-- A.3.18 on the actual rank-two binary component domain needed in 2.5.7.
The exceptional quotient is theta(H)/O₃′(theta(H)), with its original core. -/
theorem even_rank_two_dichotomy
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {L : Subgroup H} (hL : IsComponent H L) (hZ : IsPGroup 2 (center L))
    {n p : ℕ} (hn : 1 < n) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp (L ⧸ center L) 2 (2 ^ n)) :
    L = (if p = 3 then theta H else primeToResidual p H) ∨
      (p = 3 ∧ ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n) ∧
        IsPGLThree ((theta H) ⧸ pPrimeCore 3 (theta H)) (2 ^ n)) := by
  rcases hm with hlin | hsp
  · by_cases hp3 : p = 3
    · subst p
      rcases CubicLinearAction.theta_eq_or_isPGLThree_of_model hH hL hZ hn hd hlin with h | h
      · exact Or.inl (by change L = theta H; exact h)
      · exact Or.inr ⟨rfl, hlin, h⟩
    · have hp2 := hp.two_le
      have hne2 : p ≠ 2 := by
        intro he
        rw [he] at ho
        norm_num at ho
      have hlarge : 3 < p := by omega
      exact Or.inl (by
        rw [if_neg hp3]
        exact linear_component_eq_primeToResidual_of_model hH hL hZ hn hp hlarge hd hlin)
  · exact Or.inl (SymplecticResidual.component_eq_source_theta hH hL hZ hn hp ho hd hsp)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
