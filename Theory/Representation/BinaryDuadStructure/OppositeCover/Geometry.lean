module

public import Theory.Representation.BinaryAlternatingSixModels.Geometry
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The marked pentad duality of the duad–syntheme quadrangle

A syntheme lies in exactly two pentads. Their pair, relabeled by the existing
catalogue alignment, gives a bijection from synthemes to duads which intertwines
the line action with the point action twisted by the actual exceptional
six-letter automorphism. The incidence table also reverses points and lines.
The invariant polar form supplies self-duality of the opposite natural action.

The finite checks concern only the fifteen geometric objects; equivariance
for arbitrary permutations follows from the proved pentad action. These maps
are used by the middle-cover construction on the literal line-complement quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.3(5),
printed pp.343–345 (PDF pp.354–356), and the pentad construction in
GLS3, Theorem 5.2.1.
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryAlternatingSix BinaryDuadModule BinaryPermutation
open GLS3.Chapter5
namespace BinaryDuadStructure.OppositeCover

/-- The two pentads containing a syntheme, with the catalogue's marking. -/
def linePoint : Syntheme ≃ Duad where
  toFun := ![0, 9, 14, 13, 7, 1, 10, 2, 8, 4, 5, 12, 6, 3, 11]
  invFun := ![0, 5, 7, 13, 9, 10, 12, 4, 8, 1, 6, 14, 11, 3, 2]
  left_inv := by decide
  right_inv := by decide

lemma linePoint_spec (s : Syntheme) (i : Letter) :
    align i ∈ duadSet (linePoint s) ↔ synthemePartition s ∈ pentadAt i := by
  fin_cases s <;> fin_cases i <;> decide

private lemma pentad_incidence (g : S6) (s : Syntheme) (i : Letter) :
    synthemePartition (synthemeAct g s) ∈ pentadAt (outerHom g i) ↔
      synthemePartition s ∈ pentadAt i := by
  change synthemePartition (synthemeAct g s) ∈ pentadAt (outerAct g i) ↔ _
  rw [outerAct_spec]
  have he : synthemePartition (synthemeAct g s) =
      g.finsetCongr.finsetCongr (synthemePartition s) := by
    rw [synthemePartition_act]
    simp only [Equiv.finsetCongr_apply, Finset.map_eq_image, Equiv.coe_toEmbedding]
    congr 1
    funext p
    simp only [Equiv.finsetCongr_apply, Finset.map_eq_image, Equiv.coe_toEmbedding]
  rw [he]
  change g.finsetCongr.finsetCongr (synthemePartition s) ∈
    (pentadAt i).map g.finsetCongr.finsetCongr.toEmbedding ↔ _
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := Finset.mem_map.mp h
    exact g.finsetCongr.finsetCongr.injective he ▸ hx
  · intro h
    exact Finset.mem_map.mpr ⟨_, h, rfl⟩

private lemma diagram_apply (g : S6) : diagramAut g = align * outerHom g * align⁻¹ := rfl

lemma linePoint_equivariant (g : S6) (s : Syntheme) :
    linePoint (synthemeAct g s) = diagramAut g • linePoint s := by
  apply duadSet_injective
  rw [duadSet_smul]
  apply Finset.ext
  intro j
  obtain ⟨i, rfl⟩ := (align * outerHom g).surjective j
  change align (outerHom g i) ∈ duadSet (linePoint (synthemeAct g s)) ↔ _
  rw [linePoint_spec, pentad_incidence]
  have he : align (outerHom g i) = diagramAut g (align i) := by
    rw [diagram_apply]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  change _ ↔ align (outerHom g i) ∈ _
  rw [he, Finset.mem_image]
  constructor
  · intro h
    exact ⟨align i, (linePoint_spec s i).mpr h, rfl⟩
  · rintro ⟨k, hk, he⟩
    exact (linePoint_spec s i).mp ((diagramAut g).injective he ▸ hk)

/-- The dual syntheme corresponds to the point incident with its three original lines. -/
def dualLine : Syntheme → Duad := ![0, 14, 9, 12, 1, 8, 11, 7, 2, 6, 4, 10, 3, 5, 13]
lemma dual_incidence (s : Syntheme) (d : Duad) :
    incident d s ↔ incident (dualLine s) (linePoint.symm d) := by
  fin_cases s <;> fin_cases d <;> decide

/-- Incidence reversal turns a dual line sum into the original point complement. -/
lemma sum_lineComplements_dual (s : Syntheme) :
    (∑ d ∈ Finset.univ.filter (fun d => incident d s),
      lineComplement (linePoint.symm d)) = pointComplement (dualLine s) := by
  rw [pointComplement_eq_sum]
  simp only [Finset.sum_filter]
  calc
    (∑ d : Duad, if incident d s then lineComplement (linePoint.symm d) else 0) =
        ∑ d : Duad, if incident (dualLine s) (linePoint.symm d) then
          lineComplement (linePoint.symm d) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [dual_incidence s d]
    _ = _ := linePoint.symm.sum_comp
      (fun t : Syntheme => if incident (dualLine s) t then lineComplement t else 0)

/-- The preserved nondegenerate polar form identifies the opposite action with its dual. -/
noncomputable def secondSelfDual : secondAlternating.Equiv secondAlternating.dual :=
  Representation.Equiv.mk (polarForm.toDual polarForm_nondegenerate) (by
    intro g
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change polarForm (polarAction (diagramAut g.val) v) w =
      polarForm v (polarAction (diagramAut (g⁻¹).val) w)
    have he : polarAction (diagramAut g.val) (polarAction (diagramAut (g⁻¹).val) w) = w := by
      rw [← polarAction_mul, ← map_mul]
      change polarAction (diagramAut (g.val * g.val⁻¹)) w = w
      simp
    rw [← he, polarAction_form]
    rw [he])
end BinaryDuadStructure.OppositeCover
