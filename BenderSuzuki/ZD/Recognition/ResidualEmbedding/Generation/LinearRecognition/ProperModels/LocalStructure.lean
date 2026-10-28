module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.Elementary
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.LinearBorel
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.SuzukiBorel
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.Normalizers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.MixedDihedral

/-!
# Local structure for the proper residual subgroup

For `L = ⟨z,t,[O₂′(D),t]⟩`, the actual PSL₂ or Suzuki model identifies
`M ∩ L` with a Borel. Its involution core gives the elementary abelian
subgroup `A = ⟨Z ∩ M⟩` of order `2^n`, and its pair stabilizer is a cyclic
odd complement inverted by `t`. Borel conjugacy of outside involutions
then gives the genuine normalizer products `N_G(L) = LD` and `N_M(L) = TD`,
where `T` is the ambient image of the Sylow two-core of `M ∩ L`.

Odd powering identifies the complement with both `[O₂′(D),t]` and the
inverted set in `O₂′(D)`. The equality `P = Z` and exponent two of `A`
complete the mixed-involution dihedral argument, including the unique
rotation involution and the order-eight noncentralization conclusion.

The final theorem proves every clause of Lemma 12.2(b–f) from the model
alternative, `A ≤ L`, and `D ≤ N_G(L)`. Their construction and the final
assembly with clause (a) remain with the enclosing ProperModels argument.
Only local strong embedding inside `L` is used. Normality of `A` is relative
to `M`, and the Suzuki elementary subgroup is distinct from its Sylow root
group.

Source: GLS, Volume 4, Chapter 2, Lemma 12.2, using Chapter 4,
Lemma 3.2(b–e,i); `refs/KGroup/GLS4/Chapter2.tex`, lines 2007–2032,
and `refs/KGroup/GLS4/Chapter4.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The actual model alternatives supply all the Borel geometry used in
Lemma 12.2, with a common field order `2 ^ n`. -/
public theorem residualGenerated_borel_geometry_of_models
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    {n : ℕ} (hn : 2 ≤ n)
    (hmodels : Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n) ∨
      ∃ m, 1 ≤ m ∧ n = 2 * m + 1 ∧
        Nonempty (residualGenerated M z t ≃* MatrixGroups.SuzukiMatrixGroup m)) :
    let L := residualGenerated M z t
    let A := closure (Z ∩ (M : Set G))
    let B := M ⊓ L
    let E := residualPairStabilizer M t ⊓ L
    let T := (pCore 2 B).map B.subtype
    IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ n ∧
      (∃ S : Sylow 2 B, (S : Subgroup B) = pCore 2 B) ∧
      (B : Set G) = (T : Set G) * (E : Set G) ∧
      IsCyclic E ∧ Nat.card E = 2 ^ n - 1 ∧
      (∀ d ∈ E, rightConjugateElem d t = d⁻¹) ∧
      (∀ v ∈ L, PFAppendixIII.IsInvolution v → v ∉ M →
        ∃ b ∈ B, MulAut.conj b t = v) := by
  rcases hmodels with hm | ⟨m, hm, rfl, he⟩
  · obtain ⟨hA, hAc⟩ :=
      psl2_distinguishedClosure_elementary_card h.disconnected r hz hzM ht htM hL hm hn hAL
    obtain ⟨hE, hEc⟩ := psl2_local_pair_cyclic_card h.disconnected r hz hzM ht htM hL hn hm
    exact ⟨hA, hAc, psl2_local_twoCore_sylow h.disconnected r hz hzM ht htM hL hm,
      psl2_local_borel_product h.disconnected r hz hzM ht htM hL hm, hE, hEc,
      fun _ hd => psl2_local_pair_inverted h.disconnected r hz hzM ht htM hL hm hd,
      fun _ hvL hv hvM => psl2_local_involutions_conjugate
        h.disconnected r hz hzM ht htM hL hm hv hvL hvM⟩
  · exact residualGenerated_suzuki_local_structure h r hz hzM ht htM hL hAL hm he

/-- All clauses of GLS4, Chapter 2, Lemma 12.2(b–f), from the genuine
model alternatives and the containments supplied by the preceding source
argument. Normality is relative to `M`; both normalizer equalities are
carrier products; the inverted set is taken inside `O₂′(D)`.

The conclusion also retains the local involution-core identification and
normalization of `T` by `D`. The action and parity hypotheses used to
construct the model alternatives are not needed again in this passage. -/
public theorem proper_residualGenerated_local_structure_of_models
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    {n : ℕ} (hn : 2 ≤ n)
    (hmodels : Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n) ∨
      ∃ m, 1 ≤ m ∧ n = 2 * m + 1 ∧
        Nonempty (residualGenerated M z t ≃* MatrixGroups.SuzukiMatrixGroup m)) :
    let L := residualGenerated M z t
    let D := residualPairStabilizer M t
    let K := residualCommutator M t
    let A := closure (Z ∩ (M : Set G))
    let B := M ⊓ L
    let T := (pCore 2 B).map B.subtype
    closure (Z ∩ (B : Set G)) = A ∧
      (involutionCore B).map B.subtype = A ∧
      (A.subgroupOf M).Normal ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ n ∧
      Z ∩ (M : Set G) = (A : Set G) \ {1} ∧
      {v : G | PFAppendixIII.IsInvolution v ∧ ∃ x ∈ Z, ∃ y ∈ Z, v = x * y} = Z ∧
      (normalizer (L : Set G) : Set G) = (L : Set G) * (D : Set G) ∧
      centralizer (L : Set G) ≤ D ∧
      ((M ⊓ normalizer (L : Set G) : Subgroup G) : Set G) = (T : Set G) * (D : Set G) ∧
      (∃ S : Sylow 2 B, (S : Subgroup B) = pCore 2 B) ∧
      D ≤ normalizer (T : Set G) ∧
      K = D ⊓ L ∧ IsCyclic K ∧ Nat.card K = 2 ^ n - 1 ∧
      (K : Set G) = {x | x ∈ (pPrimeCore 2 D).map D.subtype ∧
        rightConjugateElem x t = x⁻¹} ∧
      (∀ u : G, PFAppendixIII.IsInvolution u → u ∉ Z →
        let H := closure ({u, z} : Set G)
        let R := zpowers (u * z)
        let w := (u * z) ^ (orderOf (u * z) / 2)
        ((∃ k : ℕ, Odd k ∧ Nat.card H = 4 * k) ∨ Nat.card H = 8) ∧
          w ∈ R ∧ PFAppendixIII.IsInvolution w ∧
          (∀ v ∈ R, PFAppendixIII.IsInvolution v → v = w) ∧
          (Nat.card H = 8 → closure ({w, z} : Set G) ≤ A ∧
            u ∈ M ∧ u ∉ centralizer (A : Set G))) := by
  obtain ⟨hA, hAc, hS, hB, hE, hEc, hinv, htrans⟩ :=
    residualGenerated_borel_geometry_of_models h r hz hzM ht htM hL hAL hn hmodels
  have hA2 : ∀ a ∈ closure (Z ∩ (M : Set G)), a ^ 2 = 1 := by
    intro a ha
    exact congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p ⟨a, ha⟩)
  have hP := involutionProducts_eq_distinguished h r hz hzM ht htM hL hAL
  have hodd : Odd (Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G)) := by
    rw [hEc]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero even_two (by omega : n ≠ 0)) odd_one
  have htI := h.disconnected.involutions t ht
  have hK := residualCommutator_eq_local_pair htI hDN hodd hinv
  have hconj : ∀ v ∈ residualGenerated M z t, v ∉ M → PFAppendixIII.IsInvolution v →
      ∃ b ∈ M ⊓ residualGenerated M z t, v = MulAut.conj b t := by
    intro v hvL hvM hv
    obtain ⟨b, hb, he⟩ := htrans v hvL hv hvM
    exact ⟨b, hb, he.symm⟩
  refine ⟨distinguishedClosure_eq_local_of_le _ hAL,
    distinguishedClosure_eq_involutionCore_local h.disconnected r hz hzM ht htM hL hAL,
    distinguishedClosure_normal h.disconnected, hA, hAc,
    distinguished_eq_nonidentity_of_exponent_two h.disconnected r hz hzM ht htM hL hAL hA2,
    hP, residual_normalizer_eq_mul_pair h r hz hzM ht htM hL hDN hconj,
    centralizer_residualGenerated_le_pairStabilizer h.disconnected hz hzM,
    residual_inter_normalizer_eq_twoCore_mul_pair htI htM hDN hB hconj,
    hS, residual_pair_le_normalizer_borel_twoCore hDN, hK, ?_, ?_,
    residualCommutator_eq_oddCore_invertedSet htI hDN hodd hinv, ?_⟩
  · rw [hK]
    exact hE
  · rw [hK]
    exact hEc
  · intro u hu huZ
    exact mixed_involution_dihedral_structure h.disconnected hz hzM hA2 hP hu huZ

end BenderSuzuki.ZD
