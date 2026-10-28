module

public import Stellmacher.Recognition.LargeTerminalLargeCore

/-!
# Full centralizer data at the upper terminal endpoint

The distinguished involution is central in the prescribed ambient Sylow.
Its full centralizer is a proper solvable two-local subgroup with trivial
odd core, and its two-core is the second local core, of order 1024.

Containment of the Sylow follows from the omega-center generator. The odd
core centralizes the normal two-core; characteristic two puts it inside
that two-core, and coprime orders force triviality. Properness follows from
ambient nonsolvability. These establish the elementary ambient hypotheses
needed by Ree centralizer recognition; they do not identify the centralizer
with a model from its order alone.

Source: Stellmacher (10.1)(18)--(20); Shinoda, A characterization of odd order
extensions of the Ree groups (1975), p.79, as audited in
`refs/original/n-group-global/large-terminal-4096-source-audit/README.md`.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix Subgroup

universe u

/-- The upper endpoint supplies a Sylow-central involution and the elementary
full-centralizer hypotheses for recognition, retaining the actual local core. -/
public theorem LargeTerminalContext.involution_centralizer_recognition_data_of_large_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hns : ¬ Group.IsSolvable G)
    (hS : Nat.card S = 4096) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S : Subgroup G) ∧
      (S : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      twoCoreIn (centralizer ({z} : Set G)) = twoCoreIn ctx.second ∧
      Nat.card (pCore 2 (centralizer ({z} : Set G))) = 1024 ∧
      pPrimeCore 2 (centralizer ({z} : Set G)) = ⊥ ∧
      Group.IsSolvable (centralizer ({z} : Set G)) ∧
      centralizer ({z} : Set G) ≠ ⊤ := by
  obtain ⟨z, hz, hgen, hcore, hcard⟩ :=
    ctx.involution_centralizer_core_eq_of_large_card hS
  let C := centralizer ({z} : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    change (S : Subgroup G) ≤ centralizer ({z} : Set G)
    rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
    exact le_centralizer_iff.mpr ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))
  obtain ⟨hsolv, hchar⟩ := ctx.localStructure C
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hz)
  have hodd : pPrimeCore 2 C = ⊥ := by
    have hle : pPrimeCore 2 C ≤ pCore 2 C :=
      (pPrimeCore_le_centralizer_of_normal_pgroup 2 (pCore 2 C)
        (pCore_isPGroup (p := 2) (G := C))).trans hchar
    obtain ⟨power, hpower⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
    have hcop : Nat.Coprime (Nat.card (pCore 2 C)) (Nat.card (pPrimeCore 2 C)) := by
      rw [hpower]
      exact (pPrimeCore_coprime_card (p := 2) (G := C)).pow_left power
    exact le_bot_iff.mp ((le_inf hle le_rfl).trans_eq
      (disjoint_of_coprime_natCard hcop).eq_bot)
  refine ⟨z, hz, hgen, hSC, hcore, hcard, hodd, hsolv, ?_⟩
  intro htop
  let _ : Group.IsSolvable C := hsolv
  apply hns
  exact Group.isSolvable_of_surjective (f := C.subtype) (by
    intro g
    refine ⟨⟨g, ?_⟩, rfl⟩
    change g ∈ centralizer ({z} : Set G)
    rw [htop]
    trivial)

end Stellmacher.Recognition
