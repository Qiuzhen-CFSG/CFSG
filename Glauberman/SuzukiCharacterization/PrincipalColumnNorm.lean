module
public import Glauberman.SuzukiCharacterization.CommutatorSupport
public import Glauberman.SuzukiCharacterization.CentralizerReduction
public import Theory.Character.ModularBlock.NormalComplementDegree
public import Theory.Character.ModularBlock.LocalColumnNorm
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# The principal-block column at the chosen central involution

A nonidentity central element of P has a centralizer containing P and having
an odd normal complement. The quotient by this complement has order |P|.
The local principal-block norm theorem and inflation through the odd complement
therefore identify the squared norm of its ambient block column with |P|.
This supplies the norm hypothesis used in the selection of the zero-fixed-space
character, without centralizer containment or trivial Sylow intersections.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 3.5 and equation (4.1), pp. 85 and 89, saved in
`refs/original/n-group-global/odd-core-rank-two-source/`.
-/

open scoped BigOperators
open Subgroup ModularBlock PrincipalBlockConstruction CompatibleBrauerBlock
noncomputable section
namespace Glauberman.SuzukiCharacterization
variable {G : Type*} [Group G] [Finite G]

private theorem quotient_card_of_normal_complement (S : Sylow 2 G)
    (N : Subgroup G) [N.Normal] (hN : Nat.Coprime 2 (Nat.card N))
    (hQ : IsPGroup 2 (G ⧸ N)) : Nat.card (G ⧸ N) = Nat.card S := by
  have hd : Disjoint (S : Subgroup G) N := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hn]; exact hN.pow_left n)
  have hc : (S : Subgroup G).IsComplement' N :=
    isComplement'_of_disjoint_and_mul_eq_univ hd (by
      apply Set.eq_univ_iff_forall.mpr
      intro x
      have hx : x ∈ (S : Subgroup G) ⊔ N := by
        rw [S.sup_eq_top_of_quotient_isPGroup N hQ]
        trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.mp hx
      exact ⟨a, ha, b, hb, rfl⟩)
  exact Nat.card_congr hc.QuotientMulEquiv.toEquiv

/-- The principal-block norm at a nonidentity central Sylow element is |P|. -/
public theorem Hypotheses.principalBlock_column_norm_of_central
    (P : Sylow 2 G) (h : Hypotheses P) (d : PrincipalCongruenceBlockData G)
    (v : P) (hv : v ≠ 1) (hz : v ∈ center P) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk (v : G)) *
      star (d.chi i (ConjClasses.mk (v : G))) = (Nat.card P : ℂ) := by
  let C := centralizer ({(v : G)} : Set G)
  have hPC : (P : Subgroup G) ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩))
  let S := P.subtype hPC
  obtain ⟨N, hN, hodd, hQ⟩ := h.centralizer_hasNormalPComplement P v v.property
    (fun he => hv (Subtype.ext he))
  let := hN
  have hcard : Nat.card (C ⧸ N) = Nat.card P := by
    rw [quotient_card_of_normal_complement S N hodd hQ]
    exact Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv
  have hp : ∃ m : ℕ, (v : G) ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := P.isPGroup'.exists_pow_pow_eq_one v
    exact ⟨m, congrArg Subtype.val hm⟩
  rw [LocalColumnNorm.principalBlock_local_column_norm d v hp,
    NormalComplementDegree.sum_degree_sq (localData d C) N
      (Nat.coprime_two_left.mp hodd) hQ, hcard]

/-- The norm hypothesis in the character-selection argument. -/
public theorem CommutatorSupportData.principalBlock_norm
    {P : Sylow 2 G} (s : CommutatorSupportData P) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) :
    ∑ i ∈ d.block, Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))) =
      (Nat.card P : ℝ) := by
  have hv : s.v ≠ 1 := by
    intro he
    simpa [he] using s.involution
  have he := h.principalBlock_column_norm_of_central P d s.v hv s.central
  simp only [Complex.star_def, Complex.mul_conj] at he
  exact_mod_cast he
end Glauberman.SuzukiCharacterization
