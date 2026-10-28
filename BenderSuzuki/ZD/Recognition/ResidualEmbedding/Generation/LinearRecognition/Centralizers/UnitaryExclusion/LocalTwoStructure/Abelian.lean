module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Definitions
public import Theory.GroupTheory.Commutator.FrattiniIrreducible
public import Theory.GroupTheory.PGroup.HomocyclicFourProduct

/-!
# The commuting two-cores and the large abelian subgroup

The literal normalizer U lies in L_B and hence centralizes the cyclic
subgroup B. The torus and two-point stabilizer normalize the literal
T = O₂(M ∩ Lᵤ). The A×B lemma, nontrivial torus movement, and irreducibility
on T/Φ(T) now prove [T,U] = 1. Multiplication of the two homocyclic
subgroups along their common involutions gives the exact two-rank 2n
and order (2ⁿ)³ of R = T₀U ≤ M.

The model actions and placement of the homocyclic subgroups remain in the
explicit `HomocyclicLocalData` premise; rank, order and [T,U] = 1 are proved
here and are not fields of that premise.
Source: GLS, volume 4, Chapter 2, Lemma 13.4 and the following construction.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

omit [Finite G] in
/-- The ambient two-core lies in the actual intersection. -/
public theorem localTwoCore_le (M H : Subgroup G) : localTwoCore M H ≤ M ⊓ H :=
  map_subtype_le _

omit [Finite G] in
/-- The ambient two-core is a two-group. -/
public theorem localTwoCore_isPGroup (M H : Subgroup G) : IsPGroup 2 (localTwoCore M H) :=
  pCore_isPGroup.map _

omit [Finite G] in
/-- Relative characteristicity gives the required ambient normalization. -/
public theorem inf_le_normalizer_localTwoCore (M H : Subgroup G) :
    M ⊓ H ≤ normalizer (localTwoCore M H : Set G) :=
  le_normalizer.trans (normalizer_le_normalizer_characteristic_image
    (M ⊓ H) (pCore 2 (M ⊓ H : Subgroup G)))

omit [Finite G] in
/-- The specified normalizer U lies in both M and L_B. -/
public theorem localU_le (B : Subgroup G) : localU Z M B u ≤ M ⊓ distinguishedCentralizer Z B :=
  inf_le_left.trans (localTwoCore_le _ _)

omit [Finite G] in
/-- The specified normalizer U is a two-group. -/
public theorem localU_isPGroup (B : Subgroup G) : IsPGroup 2 (localU Z M B u) :=
  (localTwoCore_isPGroup M (distinguishedCentralizer Z B)).to_le inf_le_left

private theorem binary_torus_coprime (n : ℕ) (hn : 0 < n) :
    Nat.Coprime 2 (2 ^ n + 1) ∧ Nat.Coprime 2 ((2 ^ n + 1) / 3) := by
  have hmod : ∀ k : ℕ, 2 ^ (k + 1) % 6 = 2 ∨ 2 ^ (k + 1) % 6 = 4 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih => rw [pow_succ]; omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hm := hmod k
  simp only [Nat.coprime_two_left, Nat.odd_iff]
  omega

omit [Finite G] in
/-- Either permitted cyclic torus order is odd for positive binary exponent. -/
public theorem torus_coprime (hn : 0 < n) (d : SecondCentralizerData Z M z t u n) :
    Nat.Coprime 2 (Nat.card d.torus) := by
  rcases d.card_torus with hc | hc
  · rw [hc]; exact (binary_torus_coprime n hn).1
  · rw [hc]; exact (binary_torus_coprime n hn).2

/-- The actual T and U commute, by the A×B and Frattini arguments. -/
public theorem local_commutator_eq_bot
    (hn : 0 < n) (d : SecondCentralizerData Z M z t u n) (hd : HomocyclicLocalData Z M z t u n d) :
    ⁅localT Z M u, localU Z M d.torus u⁆ = ⊥ := by
  have hB : d.torus ≤ M ⊓ centralizerClosure Z u :=
    le_inf (d.torus_le_pair.trans inf_le_left) d.torus_le_local
  have hD : residualPairStabilizer M t ⊓ centralizerClosure Z u ≤
      M ⊓ centralizerClosure Z u :=
    inf_le_inf inf_le_left le_rfl
  have hUB : ⁅localU Z M d.torus u, d.torus⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply (localU_le d.torus).trans (inf_le_right.trans ?_)
    exact (closure_le _).mpr (fun _ hx => hx.2)
  exact commute_of_coprime_frattini_irreducible
    (localT Z M u) (localU Z M d.torus u) d.torus
    (residualPairStabilizer M t ⊓ centralizerClosure Z u)
    (localTwoCore_isPGroup _ _) (localU_isPGroup _)
    (torus_coprime hn d) hd.U_normalizes_T
    (hB.trans (inf_le_normalizer_localTwoCore _ _)) hUB hd.torus_moves_T
    hd.torus_fixes_frattini (hD.trans (inf_le_normalizer_localTwoCore _ _))
    hd.pair_normalizes_U hd.irreducible

/-- Construct R = T₀U, deriving its abelianness, exact rank and exact order. -/
@[expose] public def largeAbelianData_of_homocyclicLocalData
    (hn : 0 < n) (d : SecondCentralizerData Z M z t u n) (hd : HomocyclicLocalData Z M z t u n d)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n) : LargeAbelianData M n := by
  let eT := Classical.choice hd.T₀_homocyclic
  let eU := Classical.choice hd.U_homocyclic
  have hcomm : hd.T₀ ≤ centralizer (localU Z M d.torus u : Set G) :=
    hd.T₀_le.trans (commutator_eq_bot_iff_le_centralizer.mp (local_commutator_eq_bot hn d hd))
  let facts := rank_card_sup_homocyclic_four
    hd.T₀ (localU Z M d.torus u) (closure (Z ∩ (M : Set G)))
    eT eU hcomm hd.intersection hcard hd.T₀_involutions hd.U_involutions
  exact { subgroup := hd.T₀ ⊔ localU Z M d.torus u
          le_pointStabilizer := sup_le
            (hd.T₀_le.trans ((localTwoCore_le _ _).trans inf_le_left))
            ((localU_le _).trans inf_le_left)
          two_group := facts.1
          abelian := facts.2.1
          rank := facts.2.2.1
          card := facts.2.2.2 }

/-- The constructed subgroup is the literal join T₀U, not an abstract model. -/
public theorem largeAbelianData_subgroup
    (hn : 0 < n) (d : SecondCentralizerData Z M z t u n)
    (hd : HomocyclicLocalData Z M z t u n d)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n) :
    (largeAbelianData_of_homocyclicLocalData hn d hd hcard).subgroup =
      hd.T₀ ⊔ localU Z M d.torus u := rfl

end BenderSuzuki.ZD.UnitaryExclusion
