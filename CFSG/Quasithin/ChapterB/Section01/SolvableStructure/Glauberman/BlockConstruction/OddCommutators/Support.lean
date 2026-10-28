module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.OddCommutators
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction

/-!
# Applying odd-core subnormality to factor supports

The pair witnesses supply the cubic cardinalities, and a rank-one minimal
offender has order two. The group-theoretic step of Kurzweil–Stellmacher
9.3.4 therefore discharges the relative-subnormality premise of
`factor_support_eq_pair`, with the original pair subgroups and action.

This is the application of 9.3.4 in 9.3.6, printed pp.242 and 244–245 of
*The Theory of Finite Groups* (`refs/original/kurzweil.pdf`). Pair recognition
(9.3.3) and cubic support separation (9.3.5) remain the independent inputs
owned by the local-block assembly.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The actual factor-support theorem with its subnormality premise discharged. -/
theorem factor_support_eq_pair_of_rank_one (hsolv : Group.IsSolvable G)
    (hρ : Function.Injective ρ) {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hrank : rank A = 1)
    (hpairs : ∀ x ∈ pPrimeCore 2 G, x ∉ centralizer (A : Set G) →
      Nonempty (PairData ρ A x))
    (hsep : CubicSupportSeparation ρ (pPrimeCore 2 G))
    {x : G} (hx : x ∈ pPrimeCore 2 G) (hxc : x ∉ centralizer (A : Set G)) :
    subspaceCommutator ρ ⊤ (⁅pPrimeCore 2 G, A⁆ ⊔ A) =
      subspaceCommutator ρ ⊤ (conjugatePair A x) := by
  have hpairCard : ∀ y ∈ pPrimeCore 2 G, y ∉ centralizer (A : Set G) →
      Nat.card ↥(conjugatePair A y ⊓ pPrimeCore 2 G) = 3 := by
    intro y hy hyc
    obtain ⟨d⟩ := hpairs y hy hyc
    exact d.odd_card
  exact factor_support_eq_pair ρ hρ hA hpairs
    (fun _ hy hyc => pair_odd_isSubnormal hsolv A
      (minimal_card ρ hA hrank) hpairCard hy hyc) hsep hx hxc

end CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
