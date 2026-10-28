module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.PrimeField

/-!
# The actual odd-characteristic E8 rank-four centralizer obstruction

A graph-stable product of two sign coroots centralizes four independent
prime-field root parameters. All words lie in the original adjoint root
group; their independence and the involution survive its actual center
quotient. The central-cover theorem applies to the original finite group,
including odd kernels divisible by the defining prime.

Source: GLS3 §§2.4 and 2.6; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.OddRankFour.E8
open Theory.AlgebraicGroup.StandardRootSystem
open TwistedE6.FoldedSubsystem.HigherRealizations
attribute [local instance] Classical.decEq
local instance : Fintype typeE8Roots := Fintype.ofFinite _

def nodes : SixNodes typeE8RootPairing_base where
  node i := typeE8RootPairing_baseEquiv (i.castLE (by decide))
  injective := by
    intro i j h
    have he := typeE8RootPairing_baseEquiv.injective h
    exact Fin.ext (congrArg (fun x : Fin 8 => x.val) he)
  cartan := by
    intro i j
    rw [typeE8RootPairing_base_cartan_apply]
    exact e8_cartan_restrict i j

variable (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Four actual prime-field coordinates inside an involution centralizer
of the literal exceptional central quotient. -/
theorem exists_elementary_centralizer (hp : p ≠ 2) :
    ∃ z : ExceptionalSplit.E8 F, orderOf z = 2 ∧
      ∃ j : (Fin 4 → Multiplicative (ZMod p)) →*
        Subgroup.centralizer ({z} : Set (ExceptionalSplit.E8 F)), Function.Injective j :=
  nodes.exists_elementary_centralizer F p hp

/-- The same concrete obstruction excludes every finite odd central cover. -/
theorem not_quasithin_of_central_cover {G : Type*} [Group G] [Finite G]
    (hp : p ≠ 2) (q : G →* ExceptionalSplit.E8 F) (hq : Function.Surjective q)
    (hc : q.ker ≤ Subgroup.center G) (ho : Odd (Nat.card q.ker)) : ¬ IsQuasithin G :=
  nodes.not_quasithin_of_central_cover F p hp q hq hc ho

end ExceptionalSplit.OddRankFour.E8
