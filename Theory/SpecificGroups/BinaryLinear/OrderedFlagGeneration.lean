module
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.InvariantSubspaces
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary

/-!
# Generation by the ordered minimal parabolics of a binary flag

The minimal parabolics of one complete binary flag generate the full linear
group. Upper elementary matrices preserve every cut, and the adjacent lower
elementary matrix at node i preserves all cuts except i. The three-index
relation generates all lower elementary matrices from these adjacent ones.
Gaussian elimination then gives the whole group. Conjugating the matrix action
by the specified basis keeps all node labels and works in every dimension
at least two.

This is the ordinary generation calculation used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March 2004,
Lemma 12.8.10(5), printed p.854 (PDF p.871), `refs/quasithin.pdf`.
The proof uses Mathlib's diagonal/transvection induction and the three-index
identity from `SLHigherNaturalFirstCohomology.Elementary`.
-/

@[expose] public section
open Subgroup
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic

private noncomputable def basisSL {m : ℕ} (b : Basis m) :
    Matrix.SpecialLinearGroup (Fin (m + 1)) (ZMod 2) ≃* LinearGroup (m + 1) :=
  (slEquivLinear (m + 1)).trans (SmallParabolicLevi.linearGroupCongr b.equivFun.symm)

private theorem basisSL_apply {m : ℕ} (b : Basis m)
    (a : Matrix.SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) (v : Space (m + 1)) :
    basisSL b a v = b.equivFun.symm ((a : Matrix _ _ _).mulVec (b.equivFun v)) := rfl

private noncomputable def flagRoot {m : ℕ} (b : Basis m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) : LinearGroup (m + 1) :=
  basisSL b (Matrix.SpecialLinearGroup.transvection hrs (1 : ZMod 2))

private theorem flagRoot_basis {m : ℕ} (b : Basis m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) (k : Fin (m + 1)) :
    flagRoot b r s hrs (b k) = if k = s then b k + b r else b k := by
  rw [flagRoot, basisSL_apply]
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec_eq, map_add]
  rw [b.equivFun_symm_apply]
  by_cases h : k = s
  · subst k
    simp
  · simp [h]

private theorem flagRoot_mem {m : ℕ} (b : Basis m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) (cuts : Set (Fin m))
    (h : ∀ i ∈ cuts, s.val ≤ i.val → r.val ≤ i.val) :
    flagRoot b r s hrs ∈ cutStabilizer b cuts := by
  rw [mem_cutStabilizer_maps]
  intro i hi v hv
  have hp : cutSpace b i ≤ (cutSpace b i).comap (flagRoot b r s hrs).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, rfl⟩
    change flagRoot b r s hrs (b k) ∈ cutSpace b i
    rw [flagRoot_basis]
    split_ifs with hks
    · exact (cutSpace b i).add_mem ((basis_mem_cutSpace b i k).mpr hk)
        ((basis_mem_cutSpace b i r).mpr (h i hi (hks ▸ hk)))
    · exact (basis_mem_cutSpace b i k).mpr hk
  exact hp hv

private theorem flagRoot_chain {m : ℕ} (b : Basis m)
    (r s t : Fin (m + 1)) (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t) :
    flagRoot b r s hrs * flagRoot b s t hst =
      flagRoot b s t hst * flagRoot b r t hrt * flagRoot b r s hrs := by
  simpa only [flagRoot, ← map_mul, one_mul] using
    congrArg (basisSL b)
      (Representation.OneCohomology.SLHigherNatural.transvection_chain hrs hst hrt
        (1 : ZMod 2) 1)

private theorem flagRoot_chain_mem {m : ℕ} (b : Basis m) (H : Subgroup (LinearGroup (m + 1)))
    (r s t : Fin (m + 1)) (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t)
    (h₁ : flagRoot b r s hrs ∈ H) (h₂ : flagRoot b s t hst ∈ H) :
    flagRoot b r t hrt ∈ H := by
  have h : flagRoot b s t hst * flagRoot b r t hrt * flagRoot b r s hrs ∈ H := by
    rw [← flagRoot_chain]
    exact H.mul_mem h₁ h₂
  exact (H.mul_mem_cancel_left h₂).mp ((H.mul_mem_cancel_right h₁).mp h)

private theorem lowerRoot_mem_join {m : ℕ} (b : Basis m)
    (r s : Fin (m + 1)) (hrs : s < r) :
    flagRoot b r s hrs.ne' ∈ ⨆ i : Fin m, minimalParabolic b i := by
  let H : Subgroup (LinearGroup (m + 1)) := ⨆ i : Fin m, minimalParabolic b i
  have hadj (k : Fin m) : flagRoot b k.succ k.castSucc (by simp [Fin.ext_iff]) ∈ H := by
    apply (le_iSup (minimalParabolic b) k)
    apply flagRoot_mem
    intro i hi hs
    change i ≠ k at hi
    have hne : i.val ≠ k.val := fun h => hi (Fin.ext h)
    change k.val + 1 ≤ i.val
    change k.val ≤ i.val at hs
    omega
  change flagRoot b r s hrs.ne' ∈ H
  induction r using Fin.induction with
  | zero => exact (Fin.not_lt_zero s hrs).elim
  | succ k ih =>
    obtain he | hlt := (Fin.le_castSucc_iff.mpr hrs).eq_or_lt
    · subst s
      exact hadj k
    · exact flagRoot_chain_mem b H k.succ k.castSucc s
        (by simp [Fin.ext_iff]) hlt.ne' hrs.ne' (hadj k) (ih hlt)

/-- The ordered minimal parabolics of a complete binary flag generate the full
linear group. Adjacent lower roots generate all lower roots by the three-index
relation; upper roots preserve every cut, and Gaussian elimination finishes. -/
theorem iSup_minimalParabolic_eq_top {m : ℕ} (hm : 1 ≤ m) (b : Basis m) :
    (⨆ i : Fin m, minimalParabolic b i) = ⊤ := by
  let H : Subgroup (LinearGroup (m + 1)) := ⨆ i : Fin m, minimalParabolic b i
  have hroot (r s : Fin (m + 1)) (hrs : r ≠ s) : flagRoot b r s hrs ∈ H := by
    rcases lt_or_gt_of_ne hrs with hlt | hgt
    · apply (le_iSup (minimalParabolic b) ⟨0, by omega⟩)
      apply flagRoot_mem
      intro i _ hs
      have : r.val < s.val := hlt
      omega
    · exact lowerRoot_mem_join b r s hgt
  let : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  apply top_unique
  intro g _
  obtain ⟨a, rfl⟩ := (basisSL b).surjective g
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
    (fun x => basisSL b x ∈ H) a ?_ ?_ ?_
  · intro i j hij c hc
    have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc
    have hd : Matrix.SpecialLinearGroup.diag2n hij c hc = 1 := by
      apply Subtype.ext
      simp [Matrix.SpecialLinearGroup.diag2n_coe, hc1]
    rw [hd, map_one]
    exact H.one_mem
  · intro i j hij c
    by_cases hc : c = 0
    · subst c
      have hz : Matrix.SpecialLinearGroup.transvection hij (0 : ZMod 2) = 1 := by
        apply Subtype.ext
        simp
      rw [hz, map_one]
      exact H.one_mem
    · rw [(by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc]
      exact hroot i j hij
  · intro x y hx hy
    simpa only [map_mul] using H.mul_mem hx hy

end BinaryLinear.InvariantNodeActions
