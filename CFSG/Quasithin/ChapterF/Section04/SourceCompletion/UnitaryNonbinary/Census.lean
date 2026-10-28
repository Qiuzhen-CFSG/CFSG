module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Valence

/-!
# The nonbinary unitary completion census

The native point count and two flag indices determine both actual projective
coset counts. The full extension order bound therefore bounds the vertex set
of any faithful completion. Its inherited unequal valencies determine the
four-walk count. For q > 2 this exceeds the vertex bound, forcing two distinct
nonbacktracking four-walks to have equal endpoints.

This is the numerical part of Aschbacher–Smith F.4.13 and F.4.24, printed
pp.280 and287. It does not identify those walks as geodesics or assert a
Hermitian recognition theorem; those source steps remain necessary.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.BasedWalk
open GreenBook.LieModels.UnitaryFour Theory.SpecificGroups.ClassicalUnitary

/-- Point and plane counts in the actual native Hermitian flag geometry. -/
def fourCosetCount (m : ℕ) (i : Bool) : ℕ :=
  ((2^m)^3+1) * (if i then 2^m+1 else (2^m)^2+1)

theorem four_native_card_coset (m : ℕ) (hm : 1 ≤ m) (i : Bool) :
    Nat.card (ProjectiveGroup m hm ⧸ SourceExtension.nativeFamily
      (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm) i) = fourCosetCount m i := by
  have hp : (pointParabolic m hm).index = ((2^m)^3+1)*((2^m)^2+1) := by
    change ((pointParabolicMatrix m hm).map (projection m hm)).index = _
    rw [Subgroup.index_map_of_bijective ⟨projection_injective m hm,
      UnitaryFourFlag.project_surjective _ _⟩]
    have h := UnitaryFourPointIndex.pointParabolic_index_eq_card (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm) m (by omega) (matrixField_card m hm) (fieldConj_apply m)
    rw [UnitaryFourPointIndex.isotropicLine_card, matrixField_card m hm,
      PointLocal.fixedField_card m hm] at h
    exact h.trans (by ring)
  cases i
  · exact hp
  · have hleft : (overlap m hm).relIndex (pointParabolic m hm) = 2^m+1 := by
      rw [← exact_overlap, relIndex, inf_subgroupOf_left]
      exact four_local_index m hm false
    have hright : (overlap m hm).relIndex (planeParabolic m hm) = (2^m)^2+1 := by
      rw [← exact_overlap, relIndex, inf_subgroupOf_right]
      exact four_local_index m hm true
    have he := (relIndex_mul_index (show overlap m hm ≤ pointParabolic m hm from
      (exact_overlap m hm) ▸ inf_le_left)).trans
      (relIndex_mul_index (show overlap m hm ≤ planeParabolic m hm from
        (exact_overlap m hm) ▸ inf_le_right)).symm
    rw [hleft, hright, hp] at he
    change (planeParabolic m hm).index = ((2^m)^3+1)*(2^m+1)
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < (2^m)^2+1)
    exact he.symm.trans (by ring)

/-- The full extension order bound bounds each literal coset orbit numerically. -/
theorem four_completion_card_coset_le (m : ℕ) (hm : 1 ≤ m) (E : FourExtension m hm)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (horder : Nat.card M ≤ Nat.card E.carrier) (i : Bool) :
    Nat.card (M ⧸ c.cosetFamily i) ≤ fourCosetCount m i := by
  let : Finite (ProjectiveGroup m hm) := Finite.of_surjective (projection m hm)
    (UnitaryFourFlag.project_surjective _ _)
  exact (E.completion_card_coset_le_native (four_conj_injective m hm)
    (parabolics_generate m hm) c horder i).trans_eq (four_native_card_coset m hm i)

/-- Four-edge nonbacktracking walks in the marked completion have the
Hermitian branching factors, even before smallness has been proved. -/
theorem four_completion_card_four_paths (m : ℕ) (hm : 1 ≤ m) (E : FourExtension m hm)
    {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) (i : Bool) :
    Nat.card {p : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily i) // p.Nonbacktracking} =
      if i then ((2^m)^2+1)*(2^m)^4 else (2^m+1)*(2^m)^5 := by
  have hc := four_completion_card_neighbors m hm E c hoverlap
  have (v : Vertex c.cosetFamily) : Finite ((graph c.cosetFamily).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases v.type <;> simp [fourDegree])
  have hf : ∀ {v w : Vertex c.cosetFamily}, (graph c.cosetFamily).Adj v w → w.type = !v.type := by
    intro v w h
    have hh := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have h := card_nonbacktracking_succ (graph c.cosetFamily)
    (fun v : Vertex c.cosetFamily => v.type) (fourDegree m) hf hc 3 (base c.cosetFamily i)
  change Nat.card {p : BasedWalk (graph c.cosetFamily) (3+1) (base c.cosetFamily i) // p.Nonbacktracking} = _
  rw [h]
  cases i <;> simp [fourDegree, forwardCount] <;> ring

/-- The genuine order bound forces two distinct four-edge walks from the
marked point to end together. Proving these walks geodesic is still a
separate native-action step; this theorem does not assert recognition. -/
theorem four_completion_four_path_collision (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m)
    (E : FourExtension m hm) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    ∃ p q : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily false),
      p.Nonbacktracking ∧ q.Nonbacktracking ∧ p.endpoint = q.endpoint ∧ p ≠ q := by
  classical
  let : Finite (Vertex c.cosetFamily) := Finite.of_equiv _ (vertexEquivSum c.cosetFamily).symm
  have hq : 4 ≤ 2^m := by
    exact pow_le_pow_right₀ (by decide : 1 ≤ 2) (by omega : 2 ≤ m)
  have hv : Nat.card (Vertex c.cosetFamily) ≤
      ((2^m)^3+1)*((2^m)^2+2^m+2) := by
    rw [Nat.card_congr (vertexEquivSum c.cosetFamily), Nat.card_sum]
    have h := Nat.add_le_add (four_completion_card_coset_le m hm E c horder false)
      (four_completion_card_coset_le m hm E c horder true)
    exact h.trans_eq (by simp only [fourCosetCount, Bool.false_eq_true, if_false, if_true]; ring)
  have hp : Nat.card (Vertex c.cosetFamily) <
      Nat.card {p : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily false) // p.Nonbacktracking} := by
    rw [four_completion_card_four_paths m hm E c hoverlap]
    apply lt_of_le_of_lt hv
    have h1 : (2^m)^3+1 ≤ 2*(2^m)^3 := by nlinarith
    have h2 : (2^m)^2+2^m+2 ≤ 2*(2^m)^2 := by nlinarith
    calc
      _ ≤ (2*(2^m)^3)*(2*(2^m)^2) := Nat.mul_le_mul h1 h2
      _ = 4*(2^m)^5 := by ring
      _ < (2^m+1)*(2^m)^5 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  have hn : ¬ Function.Injective (fun p :
      {p : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily false) // p.Nonbacktracking} =>
        p.val.endpoint) := by
    intro hi
    exact (Nat.not_le_of_gt hp) (Nat.card_le_card_of_injective _ hi)
  obtain ⟨p,q,he,hne⟩ := Function.not_injective_iff.mp hn
  exact ⟨p.val,q.val,p.property,q.property,he,fun h => hne (Subtype.ext h)⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
