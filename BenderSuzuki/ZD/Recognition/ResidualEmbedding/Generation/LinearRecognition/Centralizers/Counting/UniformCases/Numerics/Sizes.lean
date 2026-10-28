module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Inputs

/-!
# The distinguished centralizer index and the field-action square

The M-conjugacy class of z is exactly the nonidentity part of the
distinguished elementary abelian subgroup A. Its class-size formula gives
`|M| = (|A|-1)|C_G(z)|`, with the full ambient centralizer. The local field
action identifies `|A|` with the square of `|C_A(v)|` for a moving actor.
These are the denominators used in the two Thompson degree calculations.

Source: GLS4, Chapter 2, Lemmas 12.2(b), 12.4(b), and 12.8,
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
namespace ResidualNumerics

omit [Finite G] in
/-- A centralizing actor fixes the whole distinguished subgroup. -/
public theorem fixed_distinguished_eq {v : G}
    (hc : v ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G)) :
    closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) =
      closure (Z ∩ (M : Set G)) := by
  apply inf_eq_left.mpr
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc x hx)

end ResidualNumerics

/-- The full ambient centralizer of z has index |A|-1 in M. -/
public theorem proper_residualGenerated_distinguished_centralizer_card
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    Nat.card M = (Nat.card (closure (Z ∩ (M : Set G))) - 1) *
      Nat.card (centralizer ({z} : Set G)) := by
  classical
  let A := closure (Z ∩ (M : Set G))
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hZA, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  let zM : M := ⟨z, hzM⟩
  let f : {a : M // IsConj zM a} ≃ {a : A // a ≠ 1} := {
    toFun a := by
      have haZ : (a.val : G) ∈ Z := by
        obtain ⟨g, hg⟩ := isConj_iff.mp (M.subtype.map_isConj a.property)
        change g * z * g⁻¹ = (a.val : G) at hg
        rw [← hg]
        exact h.disconnected.invariant g z hz
      exact ⟨⟨a.val, subset_closure ⟨haZ, a.val.property⟩⟩,
        fun he => (h.disconnected.involutions _ haZ).ne_one (congrArg Subtype.val he)⟩
    invFun a := by
      have hne : (a.val : G) ≠ 1 := fun he => a.property (Subtype.ext he)
      have haZ : (a.val : G) ∈ Z ∩ (M : Set G) := hZA.symm ▸ ⟨a.val.property, hne⟩
      refine ⟨⟨a.val, haZ.2⟩, ?_⟩
      obtain ⟨m, hm⟩ := productDisconnected_conjugator_mem h.disconnected hz hzM haZ.1 haZ.2
      exact isConj_iff.mpr ⟨m, Subtype.ext hm⟩
    left_inv := by intro a; rfl
    right_inv := by intro a; rfl }
  have hc : Nat.card {a : M // IsConj zM a} = Nat.card A - 1 := by
    rw [Nat.card_congr f]
    let : Fintype A := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card]
  have he := ConjClasses.nat_card_carrier_mul_card_centralizer zM
  change Nat.card {a : M // IsConj zM a} * Nat.card (centralizer ({zM} : Set M)) = Nat.card M at he
  rw [hc, Nat.card_congr (TwoInvolutionClassOrder.centralizerEquiv M zM
    (h.disconnected.centralizer_le hz hzM))] at he
  exact he.symm

/-- In the moving case the same fixed-subgroup exponent gives |A| = qᵥ².
This uses the actual PSL₂ field-action alternative, not an ambient count. -/
public theorem proper_residualGenerated_moving_distinguished_card
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    {k : ℕ}
    (hfixed : Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 ^ k)
    (hc : v ∉ centralizer (closure (Z ∩ (M : Set G)) : Set G)) :
    Nat.card (closure (Z ∩ (M : Set G))) = (2 ^ k) ^ 2 := by
  have hAL := proper_residualGenerated_contains_distinguishedClosure h r ha hz hzM ht htM hL heven
  rcases hlocal.involution_action v hvD hv with hcL | ⟨j, hj, hjfixed, hm, _⟩
  · exact (hc (centralizer_le hAL hcL)).elim
  · have hjk : j = k := Nat.pow_right_injective (by decide : 2 ≤ 2)
      (hjfixed.symm.trans hfixed)
    subst j
    have hfull := (psl2_distinguishedClosure_elementary_card h.disconnected r
      hz hzM ht htM hL hm (by omega : 2 ≤ 2 * k) hAL).2
    rw [Nat.mul_comm 2 k, pow_mul] at hfull
    exact hfull

end BenderSuzuki.ZD
