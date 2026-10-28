module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Geometry
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Fusion
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Elementary
public import Theory.GroupTheory.TwoInvolutionClassOrder

/-!
# The selected involution and centralizer index for the linear count

The actual ambient centralizer of the proper residual PSL₂ has order two.
Its nonidentity element is an involution in the pair stabilizer, outside the
distinguished class. The Borel calculation identifies the nonidentity elements
of the distinguished root with the M-class of z. Class-size counting therefore
gives `|M| = (q-1)|C_G(z)|` with the full ambient centralizer.

Source: GLS, Volume 4, Chapter 2, Lemmas 12.2 and 12.8(a),
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- Select the involution used in the linear Thompson count from the actual
order-two ambient centralizer. -/
public theorem linear_counting_involution
    (h : IsProductDisconnected Z M) {z t : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (htM : t ∉ M)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2) :
    ∃ u : G, u ∈ centralizer (residualGenerated M z t : Set G) ∧
      u ∈ residualPairStabilizer M t ∧ PFAppendixIII.IsInvolution u ∧ u ∉ Z := by
  let J := centralizer (residualGenerated M z t : Set G)
  obtain ⟨u, hu, _⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJ
  have huI : PFAppendixIII.IsInvolution (u : G) := by
    refine ⟨fun he => hu (Subtype.ext he), ?_⟩
    have he := pow_card_eq_one' (x := u)
    rw [hJ] at he
    exact congrArg Subtype.val he
  have huD := centralizer_residualGenerated_le_pairStabilizer h hz hzM u.property
  exact ⟨u, u.property, huD, huI, not_mem_Z_of_mem_residualPairStabilizer h htM huD⟩

/-- The distinguished centralizer has index `q-1` in the actual stabilizer M. -/
public theorem linear_distinguished_centralizer_card
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    Nat.card M = (2 ^ n - 1) * Nat.card (centralizer ({z} : Set G)) := by
  classical
  let A := closure (Z ∩ (M : Set G))
  obtain ⟨hA, hcA⟩ := psl2_distinguishedClosure_elementary_card h r hz hzM ht htM hL ⟨e⟩ hn hAL
  have hA2 (a : G) (ha : a ∈ A) : a ^ 2 = 1 :=
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p ⟨a, ha⟩)
  have hZA := distinguished_eq_nonidentity_of_exponent_two h r hz hzM ht htM hL hAL hA2
  let zM : M := ⟨z, hzM⟩
  let f : {a : M // IsConj zM a} ≃ {a : A // a ≠ 1} := {
    toFun a := by
      have haZ : (a.val : G) ∈ Z := by
        obtain ⟨g, hg⟩ := isConj_iff.mp (M.subtype.map_isConj a.property)
        change g * z * g⁻¹ = (a.val : G) at hg
        rw [← hg]
        exact h.invariant g z hz
      exact ⟨⟨a.val, subset_closure ⟨haZ, a.val.property⟩⟩,
        fun he => (h.involutions _ haZ).ne_one (congrArg Subtype.val he)⟩
    invFun a := by
      have hne : (a.val : G) ≠ 1 := fun he => a.property (Subtype.ext he)
      have haZ : (a.val : G) ∈ Z ∩ (M : Set G) := hZA.symm ▸ ⟨a.val.property, hne⟩
      refine ⟨⟨a.val, haZ.2⟩, ?_⟩
      obtain ⟨m, hm⟩ := productDisconnected_conjugator_mem h hz hzM haZ.1 haZ.2
      exact isConj_iff.mpr ⟨m, Subtype.ext hm⟩
    left_inv := by intro a; rfl
    right_inv := by intro a; rfl }
  have hc : Nat.card {a : M // IsConj zM a} = 2 ^ n - 1 := by
    rw [Nat.card_congr f]
    let : Fintype A := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simpa only [Fintype.card_unique, ← Nat.card_eq_fintype_card] using
      congrArg (fun k : ℕ => k - 1) hcA
  have he := ConjClasses.nat_card_carrier_mul_card_centralizer zM
  change Nat.card {a : M // IsConj zM a} * Nat.card (centralizer ({zM} : Set M)) = Nat.card M at he
  rw [hc, Nat.card_congr (TwoInvolutionClassOrder.centralizerEquiv M zM
    (h.centralizer_le hz hzM))] at he
  exact he.symm
end BenderSuzuki.ZD
