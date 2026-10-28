module

public import CFSG.Quasithin.ChapterE.Section04.Basic
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer

/-!
# The solvable reduction for E.4.1

In a finite solvable group with trivial two-core, the odd core is
self-centralizing. Thus the centralization conclusion of E.3.40 excludes
every member of the second fixed-space family, giving `a ≤ 1`. In even
order Cauchy's theorem gives equality. The fixed-space centralization premise
is the earlier source theorem E.3.40 and remains explicit pending its proof;
these reductions do not assert the unconditional source theorem.

The printed equality needs the even-order qualification: E.3.9 explicitly
defines `a = 0` in odd order. The upper bound is valid in both parities.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.3.40 and
E.4.1, printed pp. 240–241.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Conditional E.4.1 reduction from E.3.40: odd-core centralization of the second fixed-space family and solvable Fitting theory imply a ≤ 1. The E.3.40 premise must still be discharged. -/
theorem moduleA_le_one_of_oddCore_centralization [Finite G]
    (ρ : Representation (ZMod 2) G V)
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (hodd : ∀ A ∈ fixedSpaceFamily ρ 2,
      A ≤ centralizer (pPrimeCore 2 G : Set G)) : moduleA ρ ≤ 1 := by
  apply (moduleA_le_iff_next_family_empty ρ 1).mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2.1.2
  exact Subgroup.not_le_centralizer_pPrimeCore_of_isPGroup 2 hsolv hcore
    (IsElementaryAbelian.isPGroup 2 A) hA.2.1.1 (hodd A hA)

/-- The even-order equality in E.4.1, conditional only on the earlier E.3.40 output. Cauchy supplies the lower bound; odd-order groups instead have a = 0. -/
theorem moduleA_eq_one_of_even_of_oddCore_centralization [Finite G]
    (ρ : Representation (ZMod 2) G V)
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (heven : Even (Nat.card G))
    (hodd : ∀ A ∈ fixedSpaceFamily ρ 2,
      A ≤ centralizer (pPrimeCore 2 G : Set G)) : moduleA ρ = 1 := by
  apply le_antisymm (moduleA_le_one_of_oddCore_centralization ρ hsolv hcore hodd)
  obtain ⟨A, hA⟩ := fixedSpaceFamily_one_nonempty_of_even ρ heven
  exact le_moduleA_of_mem ρ hA

end CFSG.Quasithin.ChapterE
