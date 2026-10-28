module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Geometry
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank

/-!
# Actual conjugation and elementary rank in the linear involution centralizer

Conjugation by a subgroup of the residual normalizer acts on the literal
residual group L. Transport by its given PSL₂ matrix equivalence constructs
the homomorphism to Aut(PSL₂); its kernel is exactly the intersection with
J = C_G(L), including both successive subgroup inclusions into M and E.
The sharp binary PSL₂ automorphism rank bounds its elementary image by q,
and |J| = 2 bounds the kernel, giving |E| ≤ 2q.

The final application derives normalization from the actual distinguished
centralizer closure C_G(u)° = L. No automorphism representation or kernel
bound is assumed. The subsequent saturation argument supplies fusion into
this centralizer; this module alone does not assert that fusion.
Source: GLS, Volume 4, Chapter 2, first paragraph of Lemma 15.7,
`refs/KGroup/GLS4/Chapter2.tex`, and Chapter 4, the PSL₂ automorphism geometry.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Conjugation on the literal residual subgroup, transported by its model equivalence. -/
@[expose] public def linearElementaryConjugation {z t : G} {n : ℕ}
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (E : Subgroup M)
    (hEN : E ≤ (normalizer (residualGenerated M z t : Set G)).subgroupOf M) :
    E →* MulAut (MatrixGroups.PSL2BinaryMatrixGroup n) :=
  (MulAut.congr e).toMonoidHom.comp
    ((residualGenerated M z t).normalizerMonoidHom.comp
      ((M.subtype.comp E.subtype).codRestrict _ (fun x => hEN x.property)))

omit [Finite G] in
/-- The kernel is the literal centralizer, restricted first to M and then to E. -/
public theorem linearElementaryConjugation_kernel {z t : G} {n : ℕ}
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (E : Subgroup M)
    (hEN : E ≤ (normalizer (residualGenerated M z t : Set G)).subgroupOf M) :
    (linearElementaryConjugation e E hEN).ker =
      ((centralizer (residualGenerated M z t : Set G)).subgroupOf M).subgroupOf E := by
  ext x
  change (MulAut.congr e) ((residualGenerated M z t).normalizerMonoidHom
    ⟨((x : M) : G), hEN x.property⟩) = 1 ↔ _
  rw [map_eq_one_iff _ (MulAut.congr e).injective]
  change ⟨((x : M) : G), hEN x.property⟩ ∈
    (residualGenerated M z t).normalizerMonoidHom.ker ↔ _
  rw [Subgroup.normalizerMonoidHom_ker]
  rfl

/-- Kernel-image counting applies the sharp rank of the actual PSL₂ automorphism group. -/
public theorem linear_elementary_normalizer_card_le {z t : G} {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (E : Subgroup M)
    (hEN : E ≤ (normalizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 2 * 2 ^ n := by
  let f := linearElementaryConjugation e E hEN
  have hpow (x : E) : x ^ 2 = 1 := Subtype.ext (hE x x.property)
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  have hk : Nat.card f.ker ≤ 2 := by
    let j : f.ker → centralizer (residualGenerated M z t : Set G) := fun x =>
      ⟨((x.val : M) : G), by
        exact (linearElementaryConjugation_kernel e E hEN).le x.property⟩
    have hj : Function.Injective j := by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun v : centralizer (residualGenerated M z t : Set G) => (v : G)) he
    exact (Nat.card_le_card_of_injective j hj).trans hJ.le
  have hr : Nat.card f.range ≤ 2 ^ n := by
    have hfpow (x : f.range) : x ^ 2 = 1 := by
      obtain ⟨a, ha⟩ := x.property
      apply Subtype.ext
      change (x : MulAut (MatrixGroups.PSL2BinaryMatrixGroup n)) ^ 2 = 1
      rw [← ha, ← map_pow, hpow, map_one]
    let : IsElementaryAbelian 2 f.range := {
      toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
        (fun x => orderOf_dvd_of_pow_eq_one (hfpow x)) a b).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hfpow }
    apply (primeRank_le_iff_elementary_card_le
      (MulAut (MatrixGroups.PSL2BinaryMatrixGroup n))).mp ?_ f.range inferInstance
    exact Theory.PSL2.BinaryAutomorphismRank.psl2_automorphism_two_rank_le hn
      (Converse.card_binaryGaloisField n (by omega))
  calc
    Nat.card E = Nat.card f.ker * Nat.card f.range := by
      rw [← Subgroup.index_ker, f.ker.card_mul_index]
    _ ≤ 2 * 2 ^ n := Nat.mul_le_mul hk hr

/-- The centralizer closure constructs normalization and supplies the bound for an
elementary subgroup centralizing the source involution. -/
public theorem linear_elementary_involution_centralizer_card_le
    (h : IsProductDisconnected Z M) {z t u : G}
    {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hu : centralizerClosure Z u = residualGenerated M z t)
    (E : Subgroup M) (hE : ∀ x ∈ E, x ^ 2 = 1)
    (hEu : ∀ x ∈ E, Commute (x : G) u) : Nat.card E ≤ 2 * 2 ^ n := by
  apply linear_elementary_normalizer_card_le hn e hJ E ?_ hE
  have hCN : centralizer ({u} : Set G) ≤ normalizer (centralizerClosure Z u : Set G) := by
    apply le_normalizer_closure_iff.mpr
    intro x hx a ha
    exact subset_closure ⟨h.invariant x a ha.1,
      (centralizer ({u} : Set G)).mul_mem
        ((centralizer ({u} : Set G)).mul_mem hx ha.2)
        ((centralizer ({u} : Set G)).inv_mem hx)⟩
  rw [hu] at hCN
  intro x hx
  exact hCN (mem_centralizer_singleton_iff.mpr (hEu x hx).eq)
end BenderSuzuki.ZD
