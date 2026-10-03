module

public import Stellmacher.MainDefs
public import FeitThompson.BGsection1.PLengthLemmas
public import FeitThompson.BGsection6.Defs

/-!
# Normal subgroups inherit characteristic 2 in the solvable case

For a finite solvable group `G` satisfying `C_G(O₂(G)) ≤ O₂(G)`, every
normal subgroup has characteristic 2. This supplies the standing Section 2
hypothesis for the normal local subgroups in the proof of Stellmacher (4.6).

The odd core of `G` centralizes its 2-core. Characteristic 2 and coprime
disjointness force that odd core to be trivial. The odd core of a normal
subgroup maps into the ambient odd core, so it is also trivial. The solvable
Fitting-centralizer theorem then gives characteristic 2 of the subgroup.

Source: `refs/latex/stellmacher-n-group.tex`, the local setup in (4.6);
the final standard implication is the special case `O_{2'}(G)=1` of
Gorenstein, Chapter 6, Theorem 3.2, already proved in the imported development.
-/

namespace Stellmacher

universe u

/-- A normal subgroup of a finite solvable characteristic-2 group has
characteristic 2. -/
public theorem characteristicTwo_normal_subgroup
    {G : Type u} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G)
    (hchar : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (N : Subgroup G) [N.Normal] : IsCharacteristicTwoType N := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddcore : pPrimeCore 2 G = ⊥ := by
    have hle : pPrimeCore 2 G ≤ pCore 2 G :=
      (pPrimeCore_le_centralizer_of_normal_pgroup 2 (pCore 2 G)
        (pCore_isPGroup (p := 2) (G := G))).trans hchar
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    have hcop : Nat.Coprime (Nat.card (pCore 2 G)) (Nat.card (pPrimeCore 2 G)) := by
      rw [hn]
      exact (pPrimeCore_coprime_card (p := 2) (G := G)).pow_left n
    have hdis := Subgroup.disjoint_of_coprime_natCard
      (H := pCore 2 G) (K := pPrimeCore 2 G) hcop
    exact le_bot_iff.mp ((le_inf hle le_rfl).trans_eq hdis.eq_bot)
  have hoddN : pPrimeCore 2 N = ⊥ := by
    have hmap : (pPrimeCore 2 N).map N.subtype ≤ pPrimeCore 2 G :=
      pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 N
    have hmapbot : (pPrimeCore 2 N).map N.subtype = ⊥ :=
      le_bot_iff.mp (hmap.trans_eq hoddcore)
    exact (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 N) N.subtype_injective).mp hmapbot
  have hsolvN : Group.IsSolvable N := by
    let _ : Group.IsSolvable G := hsolv
    infer_instance
  exact centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hsolvN hoddN

end Stellmacher
