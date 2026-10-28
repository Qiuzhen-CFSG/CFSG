module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelElementary
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The folded branch frame at a radius-three center

The label four steps to the right fixes the center and the right branch,
but exchanges its other two branches. Selecting the left endpoint, right
endpoint, and folded left endpoint therefore gives a literal branch frame.
This construction precedes the commutator relation: it is also used by the
six-point permutation calculation to identify the branch-product element.

Source: Goldschmidt (1980), (6.12.1)--(6.12.4), printed pp.403--404.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- One may select either of the two forward vertices in each ordered branch. -/
theorem CubicTreeAction.exists_branchFrame_selecting (h : CubicTreeAction F)
    (a : RankTwo.Vertex F) (e : Fin 3 ≃ (RankTwo.graph F).neighborSet a)
    (u : Fin 3 → RankTwo.Vertex F)
    (hu : ∀ i, (RankTwo.graph F).Adj (e i).val (u i)) (hua : ∀ i, u i ≠ a) :
    ∃ f : BranchFrame F a, f.e = e ∧ f.c = u := by
  classical
  obtain ⟨f⟩ := h.exists_branchFrame a
  let j : Fin 3 → Fin 3 := fun i => f.e.symm (e i)
  have he (i : Fin 3) : (f.e (j i)).val = (e i).val :=
    congrArg Subtype.val (f.e.apply_symm_apply (e i))
  have hc (i : Fin 3) : u i = f.c (j i) ∨ u i = f.d (j i) := by
    rcases f.neighbor_cases (j i) (u i) (by simpa only [he i] using hu i) with hh | hh
    · exact (hua i hh).elim
    · exact hh
  let w : Fin 3 → RankTwo.Vertex F := fun i =>
    if u i = f.c (j i) then f.d (j i) else f.c (j i)
  refine ⟨⟨e, u, w, hu, ?_, hua, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro i
    dsimp [w]
    split_ifs
    · simpa only [he i] using f.d_adj (j i)
    · simpa only [he i] using f.c_adj (j i)
  · intro i
    dsimp [w]
    split_ifs
    · exact f.d_ne_center (j i)
    · exact f.c_ne_center (j i)
  · intro i
    dsimp [w]
    split_ifs with hh
    · rw [hh]
      exact f.c_ne_d (j i)
    · exact hh
  · intro i v hv
    have hh := f.neighbor_cases (j i) v (by simpa only [he i] using hv)
    dsimp [w]
    split_ifs with hi
    · simpa only [hi] using hh
    · have hi' := (hc i).resolve_left hi
      rw [hi']
      exact hh.imp_right Or.symm

/-- The three forward points used by the source's folded commutator calculation. -/
theorem CanonicalLabelSetup.exists_radiusThree_foldedBranchFrame
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F) (hr : d.radius = 3) :
    ∃ f : BranchFrame F (d.track.vertex d.center),
      f.c = ![d.track.vertex (d.center-2), d.track.vertex (d.center+2),
        d.label (d.track.vertex (d.center+4)) • d.track.vertex (d.center-2)] := by
  classical
  let p : ℤ → RankTwo.Vertex F := fun i => d.track.vertex (d.center+i)
  let z : G := d.label (p 4)
  have hinj : Function.Injective p := by
    intro i j he
    have hh := d.track.injective he
    omega
  have hadj (i : ℤ) : (RankTwo.graph F).Adj (p i) (p (i+1)) := by
    simpa only [p, add_assoc] using d.track.adjacent (d.center+i)
  have hf (i : ℤ) : z • p i = p i ↔ 0 ≤ i ∧ i ≤ 8 := by
    dsimp only [z, p]
    rw [show d.center+4 = d.center+2*2 by omega, d.shifted_fixed_iff, hr]
    omega
  have hfix0 := (hf 0).mpr (by omega)
  have hfix1 := (hf 1).mpr (by omega)
  have hm1 : z • p (-1) ≠ p (-1) := fun he => by have := (hf (-1)).mp he; omega
  have hne : z • p (-1) ≠ p 1 := by
    intro he
    have hh := (MulAction.toPerm z).injective (he.trans hfix1.symm)
    have := hinj hh
    omega
  have hm0 : (RankTwo.graph F).Adj (p 0) (p (-1)) := by simpa using (hadj (-1)).symm
  have hm2 : (RankTwo.graph F).Adj (p (-1)) (p (-2)) := by simpa using (hadj (-2)).symm
  let e' : Fin 3 → (RankTwo.graph F).neighborSet (p 0) :=
    ![⟨p (-1), hm0⟩, ⟨p 1, hadj 0⟩,
      ⟨z • p (-1), by
        change (RankTwo.graph F).Adj (p 0) (z • p (-1))
        simpa only [hfix0] using trackGraphAction.map_adj z hm0⟩]
  have hei : Function.Injective e' := by
    intro i j hij
    have he : (e' i).val = (e' j).val := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp only [e'] at he ⊢
    all_goals first | rfl | exact (hne he).elim | exact (hne he.symm).elim |
      exact (hm1 he).elim | exact (hm1 he.symm).elim |
      (have := hinj he; omega)
  let : Finite ((RankTwo.graph F).neighborSet (p 0)) :=
    Nat.finite_of_card_ne_zero (by rw [h.card_neighbor]; decide)
  let : Fintype ((RankTwo.graph F).neighborSet (p 0)) := Fintype.ofFinite _
  have hes : Function.Surjective e' :=
    ((Fintype.bijective_iff_injective_and_card e').mpr
      ⟨hei, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, h.card_neighbor]⟩).2
  let e : Fin 3 ≃ (RankTwo.graph F).neighborSet (p 0) := Equiv.ofBijective e' ⟨hei, hes⟩
  let u : Fin 3 → RankTwo.Vertex F := ![p (-2), p 2, z • p (-2)]
  have hu (i : Fin 3) : (RankTwo.graph F).Adj (e i).val (u i) := by
    fin_cases i
    · exact hm2
    · exact hadj 1
    · exact trackGraphAction.map_adj z hm2
  have hua (i : Fin 3) : u i ≠ p 0 := by
    fin_cases i
    · intro he; have := hinj he; omega
    · intro he; have := hinj he; omega
    · intro he
      have hh := (MulAction.toPerm z).injective (he.trans hfix0.symm)
      have := hinj hh
      omega
  obtain ⟨f, _, hfc⟩ := h.exists_branchFrame_selecting (p 0) e u hu hua
  have he : ∃ f : BranchFrame F (p 0), f.c = u := ⟨f, hfc⟩
  have hp0 : p 0 = d.track.vertex d.center := by simp only [p, add_zero]
  rw [hp0] at he
  simpa only [u, p, z, sub_eq_add_neg] using he

open scoped commutatorElement
/-- The folded frame realizes the precise corrected commutator used by the
six-point action calculation, before the track relation is known. -/
theorem CanonicalLabelSetup.radiusThree_foldedBranchProduct
    (d : CanonicalLabelSetup F s) (hr : d.radius = 3)
    (f : BranchFrame F (d.track.vertex d.center))
    (hfc : f.c = ![d.track.vertex (d.center-2), d.track.vertex (d.center+2),
      d.label (d.track.vertex (d.center+4)) • d.track.vertex (d.center-2)]) :
    d.label (f.c 0) * d.label (f.c 1) * d.label (f.c 2) =
      ⁅d.label (d.track.vertex (d.center-2)), d.label (d.track.vertex (d.center+4))⁆ *
        d.label (d.track.vertex (d.center+2)) := by
  let p : ℤ → RankTwo.Vertex F := fun i => d.track.vertex (d.center+i)
  let z : ℤ → G := fun i => d.label (p i)
  have ht (k : ℤ) : (p (2*k)).type = d.side := d.shifted_type k
  have hf (k i : ℤ) : z (2*k) • p i = p i ↔ 2*k-4 ≤ i ∧ i ≤ 2*k+4 := by
    dsimp only [z, p]
    rw [d.shifted_fixed_iff, hr]
    omega
  have hc (i j : ℤ) (hlo : -2 ≤ i-j) (hhi : i-j ≤ 2) :
      Commute (z (2*i)) (z (2*j)) :=
    d.labels_commute_of_fixed (ht j) ((hf i (2*j)).2 (by omega))
  rw [hfc]
  change z (-2)*z 2*d.label (z 4 • p (-2)) = ⁅z (-2),z 4⁆*z 2
  have htm : (p (-2)).type = d.side := by simpa using ht (-1)
  have hconj : d.label (z 4 • p (-2)) = z 4*z (-2)*(z 4)⁻¹ :=
    d.conjugate (z 4) (p (-2)) htm
  have hcomm : Commute (z 2) (d.label (z 4 • p (-2))) := by
    rw [hconj]
    simpa using ((hc 1 2 (by omega) (by omega)).mul_right
      (hc 1 (-1) (by omega) (by omega))).mul_right
        (hc 1 2 (by omega) (by omega)).inv_right
  have hprod : z (-2)*d.label (z 4 • p (-2)) = ⁅z (-2), z 4⁆ := by
    rw [hconj, commutatorElement_def, d.label_inv htm]
    simp only [z, mul_assoc]
  rw [mul_assoc, hcomm.eq, ← mul_assoc, hprod]

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
