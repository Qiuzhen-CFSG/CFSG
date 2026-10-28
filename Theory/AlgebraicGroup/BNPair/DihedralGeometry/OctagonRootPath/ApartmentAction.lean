module

public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.ApartmentCycle
public import Mathlib.Data.Set.Card

/-!
# Oriented edges in the actual normalizer apartment

A marked simple reflection fixes its own standard vertex and moves the other
one. In an apartment having two neighbors per vertex these are its two possible
edge directions. Normalizer representatives therefore act transitively on
oriented apartment edges of each fixed initial type. The later girth argument
supplies the stated two-neighbor condition from the actual sixteen-cycle.

Source: the dihedral apartment action in GLS3 §§2.3 and 2.6.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open Subgroup SimpleGraph
open scoped Pointwise
variable {X I : Type*} [Group X] {T : TitsSystem (X := X)} {F : I → Subgroup X}

namespace OctagonalDatum
variable (D : OctagonalDatum T F)

private theorem pair_of_ncard_two {V : Type*} (s : Set V) (hs : s.ncard = 2)
    {a b c : V} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) :
    c = a ∨ c = b := by
  obtain ⟨x, y, _, hxy⟩ := Set.ncard_eq_two.mp hs
  simp only [hxy, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
  aesop

/-- Normalizer translations preserve the actual standard apartment. -/
theorem normalizer_mem_apartment (n : T.N) {v : CosetGeometry.Vertex F}
    (hv : v ∈ apartment T F) : (n : X) • v ∈ apartment T F := by
  obtain ⟨a, ha, i, rfl⟩ := hv
  exact ⟨(n : X) * a, T.N.mul_mem n.property ha, i, mul_smul _ _ _⟩

include D in
/-- A marked reflection gives the two distinct standard apartment directions. -/
theorem exists_reflection_neighbors (i j : I) (hij : i ≠ j) :
    ∃ n : T.N, (n : X) • CosetGeometry.base F i = CosetGeometry.base F i ∧
      (n : X) • CosetGeometry.base F j ≠ CosetGeometry.base F j := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective ((T.B ⊓ T.N).subgroupOf T.N) (D.simple i)
  have hi : (n : X) ∈ F i := (D.representative_mem_parabolic_iff i n).mpr (Or.inr hn)
  refine ⟨n, ?_, ?_⟩
  · apply MulAction.mem_stabilizer_iff.mp
    rwa [CosetGeometry.stabilizer_base]
  · intro he
    have hj : (n : X) ∈ F j := by
      rw [← CosetGeometry.stabilizer_base F j]
      exact MulAction.mem_stabilizer_iff.mpr he
    rcases (D.representative_mem_parabolic_iff j n).mp hj with h1 | hj
    · exact ((T.involutions _ (D.simple_mem i)).1) (hn.symm.trans h1)
    · exact hij (D.simple_injective (hn.symm.trans hj))

include D in
/-- An apartment edge has a simultaneous representative in the actual normalizer. -/
theorem normalizer_edge_representative
    (hdeg : ∀ v ∈ apartment T F,
      {w | w ∈ apartment T F ∧ (graph F).Adj v w}.ncard = 2)
    {u v : CosetGeometry.Vertex F} (hu : u ∈ apartment T F)
    (hv : v ∈ apartment T F) (hadj : (graph F).Adj u v) :
    ∃ n : T.N, (n : X) • CosetGeometry.base F u.type = u ∧
      (n : X) • CosetGeometry.base F v.type = v := by
  obtain ⟨a, ha, i, rfl⟩ := hu
  let aN : T.N := ⟨a, ha⟩
  let v' := a⁻¹ • v
  have hv' : v' ∈ apartment T F := normalizer_mem_apartment aN⁻¹ hv
  have hadj' : (graph F).Adj (CosetGeometry.base F i) v' := by
    simpa only [smulHom_apply, inv_smul_smul] using (smulHom F a⁻¹).map_rel hadj
  have hij : i ≠ v.type := hadj.1
  obtain ⟨n, hni, hnj⟩ := D.exists_reflection_neighbors i v.type hij
  let b := CosetGeometry.base F v.type
  have hb : b ∈ apartment T F ∧ (graph F).Adj (CosetGeometry.base F i) b :=
    ⟨base_mem_apartment F T _, hij, CosetGeometry.incident_base F _ _⟩
  have hnB : (n : X) • b ∈ apartment T F ∧
      (graph F).Adj (CosetGeometry.base F i) ((n : X) • b) := by
    refine ⟨normalizer_mem_apartment n hb.1, ?_⟩
    have hh := (smulHom F (n : X)).map_rel hb.2
    simpa only [smulHom_apply, hni] using hh
  have hvchoice : v' = b ∨ v' = (n : X) • b := pair_of_ncard_two _
    (hdeg _ (base_mem_apartment F T i)) hb hnB ⟨hv', hadj'⟩ hnj.symm
  rcases hvchoice with he | he
  · refine ⟨aN, rfl, ?_⟩
    simpa only [v', smul_inv_smul] using (congrArg (a • ·) he).symm
  · refine ⟨aN * n, ?_, ?_⟩
    · change (a * (n : X)) • CosetGeometry.base F i = a • CosetGeometry.base F i
      rw [mul_smul, hni]
    · change (a * (n : X)) • b = v
      simpa only [v', mul_smul, smul_inv_smul] using (congrArg (a • ·) he).symm

end OctagonalDatum
end Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
