module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerActors
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.SmallPrime
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.LargePrime
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.FourAction

/-!
# Inner PSU₃ involution centralizers: local structure and its consumer

The p = 3 centralizer is solvable in every ambient two-extension. For p > 3,
its residual supplement has the proved SL₂ residual, two-group radical,
two-group layer quotient, residual equality, and single-component local-tau
orbit. The abelian centralizer of the inner four-group proves that it survives
the radical quotient, giving the component commutator alternative.

The local structure and the concrete large-family containment consumer are
unconditional. The proof works for any normal PSU₃(p) supplemented by the
ambient Sylow subgroup, so includes all the source's simple generalized
Fitting subgroups and SQTK two-extensions. The parent retains the final
generation contradiction for E.1.14(7).

Source: Aschbacher--Smith E.1.2, E.1.14(7), pp.210,214; A.3.21(a), p.55;
Aschbacher, GF(2)-representations of finite groups (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
variable {G : Type*} [Group G] [Finite G]

/-- The exact local alternative: solvability at p = 3 and the literal E₂
component case on C_G(z)^∞T at p > 3, in every ambient two-extension. -/
theorem inner_centralizer_local_structure
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hfour : Nat.card A = 4)
    (hAT : A ≤ (T : Subgroup G)) (hAL : A ≤ L)
    (z : G) (hzA : z ∈ A) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    Group.IsSolvable (centralizer ({z} : Set G)) ∨
      ECaseComponent (T : Subgroup G) A (centralizerResidualOvergroup T z) := by
  by_cases hthree : p = 3
  · subst p
    exact Or.inl (inner_centralizer_solvable_of_prime_three L T hLT hmodel z (hAL hzA) hz)
  · have hlarge : 3 < p := by
      have hp2 := hp.two_le
      have hnot2 : p ≠ 2 := by intro h; subst p; norm_num at hodd
      omega
    let := hA
    exact Or.inr (inner_centralizer_component_of_not_le_radical L T hLT hp hodd hlarge
      hmodel A z (hAL hzA) hz hTz
      (inner_four_not_le_centralizerResidual_radical L T hLT hp hodd hlarge hmodel A
        hfour hAT hAL z hz hzA hTz))

/-- The actual large-family consumer: one inner member forces a Sylow-central
socle involution whose full centralizer lies in the obstruction overgroup. -/
theorem exists_inner_centralizer_le
    (L : Subgroup G) [L.Normal] {T : Sylow 2 G}
    (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    (d : LargeFamilyObstruction T)
    (hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ A ≤ L) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ L ∧ z ∈ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ≤ d.overgroup := by
  apply exists_inner_centralizer_le_of_local_structure L hp hodd hmodel d hi
  intro A hA hAT hne hAL z hz _hzL hTz hzA
  exact inner_centralizer_local_structure L T hLT hp hodd hmodel A (d.elementary.1 A hA)
    (inner_member_card_eq_four L hp hodd hmodel d hA hAT hne hAL) hAT hAL z hzA hz hTz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
