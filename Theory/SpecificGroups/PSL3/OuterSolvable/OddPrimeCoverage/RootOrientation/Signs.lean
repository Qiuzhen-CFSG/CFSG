module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootRigidity
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.UnipotentGeometry

/-!
# Coordinate signs and the A₂ opposition symmetry

The three diagonal sign involutions label the pairs of opposite roots: the
root with indices omitting k is the centralizer of sign k inside a unipotent
subgroup. Once these geometric identities and the permutation of signs are
known, the central highest root forces that permutation to fix its label.
There are only two remaining permutations, exchanged by coordinate reversal
and inverse transpose.

This module proves that reduction and the explicit matrix actions. The sign
centralizers and permutation are discharged in the adjoining modules.
Source: GLS3, Theorem 2.5.12(a) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115.
-/

@[expose] public section

open scoped MatrixGroups
open Matrix
namespace Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable {F : Type*} [Field F]

def signSL (k : Fin 3) : SL(3,F) :=
  ⟨Matrix.diagonal (fun i => if i = k then 1 else -1), by
    fin_cases k <;> simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

def signElement (k : Fin 3) : PSL(3,F) := QuotientGroup.mk (signSL (F := F) k)

theorem signElement_sq (k : Fin 3) : signElement (F := F) k ^ 2 = 1 := by
  have h : signSL (F := F) k * signSL k = 1 := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => if i = k then (1 : F) else -1) *
      Matrix.diagonal (fun i => if i = k then (1 : F) else -1) = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hi : i = k <;> by_cases hj : j = k <;> by_cases hij : i = j <;>
      simp_all [Matrix.one_apply]
  simpa only [signElement, pow_two, ← QuotientGroup.mk_mul, QuotientGroup.mk_one] using
    congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F)) h

def rootFirst : Fin 3 → Fin 3 := ![1,0,0]
def rootSecond : Fin 3 → Fin 3 := ![2,2,1]

theorem rootFirst_ne_second (k : Fin 3) : rootFirst k ≠ rootSecond k := by
  fin_cases k <;> decide

def positiveRoot (k : Fin 3) : Subgroup PSL(3,F) := rootGroup (rootFirst_ne_second k)
def negativeRoot (k : Fin 3) : Subgroup PSL(3,F) := rootGroup (rootFirst_ne_second k).symm

theorem graph_rootElement {i j : Fin 3} (hij : i ≠ j) (a : F) :
    graph F (rootElement hij a) = rootElement hij.symm (-a) := by
  rw [rootElement, graph_mk]
  have h : SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij.symm a := by
    apply Subtype.ext
    simp [SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_single]
  rw [h, SpecialLinearGroup.transvection_inv]
  rfl

theorem linearConj_reversal_rootElement {i j : Fin 3} (hij : i ≠ j) (a : F) :
    linearConj F (reversalGL F) (rootElement hij a) =
      rootElement (Fin.rev_injective.ne hij) a := by
  change QuotientGroup.mk (linearConjSL F (reversalGL F)
    (SpecialLinearGroup.transvection hij a)) = _
  apply congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F))
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  apply Units.ext
  change (reversalGL F).val * (1 + Matrix.single i j a) * (reversalGL F).inv =
    1 + Matrix.single i.rev j.rev a
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [reversalGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.single_apply,
        Matrix.one_apply, Fin.rev]

theorem oppositionGraph_rootElement {i j : Fin 3} (hij : i ≠ j) (a : F) :
    oppositionGraph F (rootElement hij a) =
      rootElement (Fin.rev_injective.ne hij.symm) (-a) := by
  rw [oppositionGraph, MulAut.mul_apply, graph_rootElement, linearConj_reversal_rootElement]

theorem oppositionGraph_sq : oppositionGraph F ^ 2 = 1 := by
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext
  intro i j hij a
  change (oppositionGraph F * oppositionGraph F) (rootElement hij a) = rootElement hij a
  simp only [MulAut.mul_apply, oppositionGraph_rootElement, Fin.rev_rev, neg_neg]

theorem oppositionGraph_rootGroup {i j : Fin 3} (hij : i ≠ j) :
    (rootGroup (F := F) hij).map (oppositionGraph F).toMonoidHom =
      rootGroup (Fin.rev_injective.ne hij.symm) := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨Multiplicative.ofAdd (-a.toAdd), oppositionGraph_rootElement hij a.toAdd |>.symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨rootElement hij (-a.toAdd), rootElement_mem hij _, ?_⟩
    change oppositionGraph F (rootElement hij (-a.toAdd)) =
      rootElement (Fin.rev_injective.ne hij.symm) a.toAdd
    rw [oppositionGraph_rootElement, neg_neg]

theorem oppositionGraph_positiveRoot (k : Fin 3) :
    (positiveRoot (F := F) k).map (oppositionGraph F).toMonoidHom = positiveRoot k.rev := by
  rw [positiveRoot, oppositionGraph_rootGroup]
  fin_cases k <;> rfl

theorem oppositionGraph_negativeRoot (k : Fin 3) :
    (negativeRoot (F := F) k).map (oppositionGraph F).toMonoidHom = negativeRoot k.rev := by
  rw [negativeRoot, oppositionGraph_rootGroup]
  fin_cases k <;> rfl

theorem preservesRootGroups_of_root_pairs (α : MulAut PSL(3,F))
    (hpos : ∀ k, (positiveRoot (F := F) k).map α.toMonoidHom = positiveRoot k)
    (hneg : ∀ k, (negativeRoot (F := F) k).map α.toMonoidHom = negativeRoot k) :
    PreservesRootGroups α := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  · exact hpos 2
  · exact hpos 1
  · exact hneg 2
  · exact hpos 0
  · exact hneg 1
  · exact hneg 0

private theorem perm_three_fix_one (σ : Equiv.Perm (Fin 3)) (h : σ 1 = 1) :
    (∀ k, σ k = k) ∨ (∀ k, σ k = k.rev) := by
  have h01 : σ 0 ≠ 1 := by
    rw [← h]
    exact σ.injective.ne (by decide)
  have h21 : σ 2 ≠ 1 := by
    rw [← h]
    exact σ.injective.ne (by decide)
  have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have hcases : σ 0 = 0 ∨ σ 0 = 2 := by omega
  rcases hcases with h0 | h0
  · have h2 : σ 2 = 2 := by omega
    left
    intro k
    fin_cases k <;> assumption
  · have h2 : σ 2 = 0 := by omega
    right
    intro k
    fin_cases k <;> assumption

theorem exists_oppositionGraph_of_root_permutation (α : MulAut PSL(3,F))
    (σ : Equiv.Perm (Fin 3)) (hσ : σ 1 = 1)
    (hpos : ∀ k, (positiveRoot (F := F) k).map α.toMonoidHom = positiveRoot (σ k))
    (hneg : ∀ k, (negativeRoot (F := F) k).map α.toMonoidHom = negativeRoot (σ k)) :
    ∃ ε : Fin 2, PreservesRootGroups ((oppositionGraph F ^ (ε : ℕ))⁻¹ * α) := by
  rcases perm_three_fix_one σ hσ with hid | hrev
  · refine ⟨0, ?_⟩
    simp only [Fin.val_zero, pow_zero, inv_one, one_mul]
    apply preservesRootGroups_of_root_pairs α
    · intro k
      rw [hpos, hid]
    · intro k
      rw [hneg, hid]
  · have hinv : (oppositionGraph F)⁻¹ = oppositionGraph F :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using oppositionGraph_sq (F := F))
    refine ⟨1, ?_⟩
    simp only [Fin.val_one, pow_one, hinv]
    apply preservesRootGroups_of_root_pairs
    · intro k
      change (positiveRoot k).map
        ((oppositionGraph F).toMonoidHom.comp α.toMonoidHom) = _
      rw [← Subgroup.map_map, hpos, hrev, oppositionGraph_positiveRoot, Fin.rev_rev]
    · intro k
      change (negativeRoot k).map
        ((oppositionGraph F).toMonoidHom.comp α.toMonoidHom) = _
      rw [← Subgroup.map_map, hneg, hrev, oppositionGraph_negativeRoot, Fin.rev_rev]

theorem map_inf_centralizer_singleton {G : Type*} [Group G]
    (H : Subgroup G) (t : G) (α : MulAut G) :
    (H ⊓ Subgroup.centralizer {t}).map α.toMonoidHom =
      H.map α.toMonoidHom ⊓ Subgroup.centralizer {α t} := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, ht⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hy, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change α y * α t = α t * α y
    simpa only [map_mul] using congrArg α (Subgroup.mem_centralizer_singleton_iff.mp ht)
  · rintro ⟨⟨y, hy, rfl⟩, ht⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply α.injective
    simp only [map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp ht

private theorem map_le_centralizer_of_preserves {G : Type*} [Group G]
    (H U : Subgroup G) (α : MulAut G) (hU : U.map α.toMonoidHom = U)
    (h : H ≤ Subgroup.centralizer (U : Set G)) :
    H.map α.toMonoidHom ≤ Subgroup.centralizer (U : Set G) := by
  rintro x ⟨x, hx, rfl⟩ y hy
  rw [← hU] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  change α y * α x = α x * α y
  simpa only [map_mul] using congrArg α (h hx y hy)

theorem exists_oppositionGraph_of_sign_geometry (α : MulAut PSL(3,F))
    (hα : PreservesUnipotentPair F α)
    (hperm : ∃ σ : Equiv.Perm (Fin 3), ∀ k, α (signElement k) = signElement (σ k))
    (hpos : ∀ k, upperUnipotent F ⊓ Subgroup.centralizer {signElement k} = positiveRoot k)
    (hneg : ∀ k, lowerUnipotent F ⊓ Subgroup.centralizer {signElement k} = negativeRoot k)
    (hcentral : ∀ k, positiveRoot (F := F) k ≤
      Subgroup.centralizer (upperUnipotent F : Set PSL(3,F)) ↔ k = 1) :
    ∃ ε : Fin 2, PreservesRootGroups ((oppositionGraph F ^ (ε : ℕ))⁻¹ * α) := by
  obtain ⟨σ, hσ⟩ := hperm
  have hp (k : Fin 3) : (positiveRoot k).map α.toMonoidHom = positiveRoot (σ k) := by
    rw [← hpos, map_inf_centralizer_singleton, hα.1, hσ, hpos]
  have hn (k : Fin 3) : (negativeRoot k).map α.toMonoidHom = negativeRoot (σ k) := by
    rw [← hneg, map_inf_centralizer_singleton, hα.2, hσ, hneg]
  have hfix : σ 1 = 1 := by
    apply (hcentral (σ 1)).mp
    rw [← hp]
    exact map_le_centralizer_of_preserves _ _ α hα.1 ((hcentral 1).mpr rfl)
  exact exists_oppositionGraph_of_root_permutation α σ hfix hp hn

theorem signSL_sq (k : Fin 3) : signSL (F := F) k ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change Matrix.diagonal (fun i => if i = k then (1 : F) else -1) *
    Matrix.diagonal (fun i => if i = k then (1 : F) else -1) = 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = k <;> by_cases hij : i = j <;> simp_all [Matrix.one_apply]

theorem signSL_inv (k : Fin 3) : (signSL (F := F) k)⁻¹ = signSL k :=
  inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using signSL_sq (F := F) k)

theorem graph_signElement (k : Fin 3) : graph F (signElement k) = signElement k := by
  rw [signElement, graph_mk]
  have ht : SpecialLinearGroup.transpose (signSL (F := F) k) = signSL k := by
    apply Subtype.ext
    exact Matrix.diagonal_transpose _
  rw [ht, signSL_inv]

theorem signElement_ne_one (h2 : (2 : F) ≠ 0) (k : Fin 3) :
    signElement (F := F) k ≠ 1 := by
  intro h
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp
    ((QuotientGroup.eq_one_iff _).mp h)
  have h0 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) hr
  have h1 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 1 1) hr
  fin_cases k <;> simp [signSL, Matrix.scalar] at h0 h1
  · apply h2
    linear_combination h1 - h0
  · apply h2
    linear_combination h0 - h1
  · have h2' := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 2) hr
    simp [signSL, Matrix.scalar] at h2'
    apply h2
    linear_combination h0 - h2'

theorem signElement_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (signElement (F := F)) := by
  intro k l h
  by_contra hn
  have hc : signSL (F := F) l * signSL k ∈ Subgroup.center SL(3,F) := by
    have he : (projection F) (signSL k) = (projection F) (signSL l) := h
    have hm := (projection F).eq_iff.mp he
    rw [projection_ker, signSL_inv] at hm
    exact hm
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  change Matrix.scalar (Fin 3) r =
    Matrix.diagonal (fun i => if i = l then (1 : F) else -1) *
    Matrix.diagonal (fun i => if i = k then (1 : F) else -1) at hr
  rw [Matrix.diagonal_mul_diagonal] at hr
  have h0 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) hr
  have h1 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 1 1) hr
  have h2' := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 2) hr
  fin_cases k <;> fin_cases l
  all_goals try exact (hn rfl).elim
  all_goals
    simp [Matrix.scalar] at h0 h1 h2'
    apply h2
    first | linear_combination h0 - h1 | linear_combination h1 - h0 |
      linear_combination h0 - h2'

end Matrix.PSL3.OuterSolvable.OddPrimeCoverage
