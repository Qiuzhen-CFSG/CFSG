module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.AbelianClosure
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus

/-!
# The final hyperplane obstruction in the unitary closure argument

If a hyperplane in a conjugate of `V` induces rank at most two on `V`,
its centralizer kernel has corank at most three in that conjugate.
The source bound `r(G,V)>3` forces `V` to normalize the conjugate, making
their join a two-group. The literal F.9 application uses `Vᵍ∩Q_H` and
transports its corank through the original conjugation map.

This isolates the last contradiction of Aschbacher–Smith, Lemma 13.3.18,
printed p.895. The preceding point-parabolic calculations must still
establish the hyperplane and rank-at-most-two image for the chosen pair.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The last rank obstruction in 13.3.18: a hyperplane in the conjugate
with action image of rank at most two forces the whole pair to be a two-group. -/
theorem pair_isTwo_of_hyperplane_action
    {V : Subgroup G} [IsElementaryAbelian 2 V] (g : G)
    {B : Subgroup G} (hBW : B ≤ V.map (MulAut.conj g).toMonoidHom)
    (hBN : B ≤ normalizer (V : Set G))
    (hhyper : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B ≤ 1)
    (himage : rank (inducedAutomizer V B) ≤ 2)
    (hr : (3 : ℕ∞) < globalR V) :
    IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let C := B ⊓ centralizer (V : Set G)
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 B := offender_elementary_of_le hBW
  have hCW : C ≤ W := inf_le_left.trans hBW
  have hcor : subgroupCorank W C ≤ 3 := by
    rw [offender_corank_add (B := C) inf_le_left hBW,
      ← rank_inducedAutomizer V B hBN]
    omega
  have hVN : V ≤ normalizer (W : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (V : Set G) from inf_le_right)).trans
      (centralizer_le_normalizer_of_corank_lt_globalR hCW
        (by rw [globalR_map_equiv]; exact lt_of_le_of_lt (by exact_mod_cast hcor) hr))
  rw [sup_comm]
  exact (IsElementaryAbelian.isPGroup 2 W).to_sup_of_normal_left'
    (IsElementaryAbelian.isPGroup 2 V) hVN

/-- The same obstruction applied to the literal source hyperplane
`Vᵍ∩Q_H`; its invariance comes from F.9.2 and T-invariance of V. -/
theorem source_pair_image_rank_three
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (g : G) (hg : g ∈ D.H)
    (hhyper : subgroupCorank D.V (D.V ⊓ D.QH) ≤ 1)
    (hr : (3 : ℕ∞) < globalR D.V)
    (hpair : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    3 ≤ rank (inducedAutomizer D.V
      (D.V.map (MulAut.conj g).toMonoidHom ⊓ D.QH)) := by
  let := h.elementary
  have hQ : D.QH.map (MulAut.conj g).toMonoidHom = D.QH :=
    mem_normalizer_iff_map_conj_eq.mp
      (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D) hg)
  have hcor : subgroupCorank (D.V.map (MulAut.conj g).toMonoidHom)
      (D.V.map (MulAut.conj g).toMonoidHom ⊓ D.QH) ≤ 1 := by
    rw [← hQ, ← map_inf _ _ _ (MulAut.conj g).injective]
    unfold subgroupCorank
    rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hhyper
  by_contra hn
  have himage : rank (inducedAutomizer D.V
      (D.V.map (MulAut.conj g).toMonoidHom ⊓ D.QH)) ≤ 2 := by omega
  exact hpair (pair_isTwo_of_hyperplane_action g inf_le_left
    (inf_le_right.trans (h.QH_le_T.trans h.T_normalizes_V)) hcor himage hr)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
