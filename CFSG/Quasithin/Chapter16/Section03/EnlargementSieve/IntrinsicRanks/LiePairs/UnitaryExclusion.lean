module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Contracts
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Geometry
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Rank
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.Bounds
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts

/-!
# Applying the earlier unitary exclusion to the actual enlargement

The component and commutator clauses of 16.1.7(3) place the actual pair in
the precise setup of 16.3.4. The two involutions are already in the required
position, and the original involution centralizes L⟨t⟩. The earlier exclusion
can therefore be applied to a full PSU₃ model. Passing from a central
quotient model additionally requires, and uses, the proved centerlessness
of K; a quotient tag alone is insufficient.

Source: Aschbacher–Smith, 16.3.4 and 16.3.9, printed pp.1178 and 1180.
The earlier exclusion remains an explicit source input.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs
open FourGroupTransfer
variable {G : Type*} [Group G] {T : Sylow 2 G}
  {z t : G} {L : Subgroup G}

/-- All hypotheses of the earlier exclusion, retaining relative component
membership and the actual commutator equality. -/
theorem unitary_exclusion_setup (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hL : ComponentTransfer.IsComponentIn L
      (ComponentTransfer.centralizerIn (enlargement t L) z))
    (hcomm : ⁅enlargement t L, zpowers z⁆ = enlargement t L) :
    ExclusionSetup T z L (enlargement t L) t z := by
  refine ⟨h.localSetup, h.normal, h.involution, h.mem_commutingSylow,
    hK, h.localSetup.involution, hL, ?_, hcomm⟩
  have hsup : L ⊔ zpowers t ≤ involutionCentralizer z :=
    sup_le h.localSetup.component.1
      (zpowers_le.mpr (h.localSetup.sylow_centralizes h.mem_commutingSylow.1))
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hsup hx)

/-- The unitary model is excluded by the literal earlier 16.3.4 statement. -/
theorem exclude_simple_unitary
    (exclude : ∀ (J : Subgroup G) (a b : G),
      ExclusionSetup T z L J a b → ¬ IsExcludedSimple J)
    (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hL : ComponentTransfer.IsComponentIn L
      (ComponentTransfer.centralizerIn (enlargement t L) z))
    (hcomm : ⁅enlargement t L, zpowers z⁆ = enlargement t L)
    {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSU (enlargement t L) 3 (2 ^ n)) : False :=
  exclude _ _ _ (unitary_exclusion_setup h hK hL hcomm) (Or.inl ⟨n, hn, hmodel⟩)

/-- Use the quotient model only after transporting across the actual
centerless quotient isomorphism. -/
theorem exclude_centerless_unitary_quotient
    (exclude : ∀ (J : Subgroup G) (a b : G),
      ExclusionSetup T z L J a b → ¬ IsExcludedSimple J)
    (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hL : ComponentTransfer.IsComponentIn L
      (ComponentTransfer.centralizerIn (enlargement t L) z))
    (hcomm : ⁅enlargement t L, zpowers z⁆ = enlargement t L)
    {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSU
      (enlargement t L ⧸ center (enlargement t L)) 3 (2 ^ n))
    (hZ : center (enlargement t L) = ⊥) : False := by
  apply exclude_simple_unitary exclude h hK hL hcomm hn
  exact hmodel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs
