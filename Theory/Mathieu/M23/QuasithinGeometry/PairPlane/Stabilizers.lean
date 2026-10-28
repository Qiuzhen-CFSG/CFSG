module

public import Theory.Mathieu.M23.QuasithinGeometry.Design

/-!
# Stabilizers in the pair-derived M23 geometry

Stabilizing both adjacent pairs fixes each of their three points. Hence the
intersection is the stabilizer of the remaining plane point inside the
pointwise pair stabilizer. Recovering a heptad by adjoining the deleted pair
identifies the pair/heptad intersection with the derived-line stabilizer.
A second certified heptad separates the deleted points and proves faithfulness
of the action on the complement.

These identifications retain the natural point and line action maps. Their
transport to field coordinates supplies the two parabolics used in
Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.2,
Lemmas 5.2.18 and 5.2.20, printed pp.655--656. The coordinate and matrix-group
identifications are separate results.
-/

@[expose] public section

open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry

/-- The kernel of the action on the two deleted points. -/
noncomputable abbrev pointwisePairStabilizer : Subgroup pairStabilizer :=
  (setAction x.val).ker

/-- The plane point selected by the adjacent vertex y. -/
def adjacentPoint : pairComplement x.val := ⟨label 4, by decide +kernel⟩

/-- The plane line selected by the distinguished heptad. -/
noncomputable def omegaLine : pairLines x.val :=
  ⟨omega \ x.val, mem_pairLines.mpr ⟨omega, omega_mem,
    x_subset_lambda.trans lambda_subset_omega, rfl⟩⟩

theorem adjacentPoint_mem_omegaLine : adjacentPoint.val ∈ omegaLine.val := by
  decide +kernel

theorem mem_pointwisePairStabilizer (g : pairStabilizer) :
    g ∈ pointwisePairStabilizer ↔
      (g : M23) • label 5 = label 5 ∧ (g : M23) • label 6 = label 6 := by
  rw [mem_setAction_ker]
  simp [x]

/-- Inside the pair stabilizer, the adjacent-pair stabilizer is the point
stabilizer in the kernel of the deleted-pair action. -/
theorem mem_adjacent_stabilizer_iff (g : pairStabilizer) :
    (g : M23) ∈ MulAction.stabilizer M23 y.val ↔
      g ∈ pointwisePairStabilizer ∧
        complementAction x.val g adjacentPoint = adjacentPoint := by
  have hx : (g : M23) • x.val = x.val :=
    MulAction.mem_stabilizer_iff.mp g.property
  have hxy : x.val ∩ y.val = {label 5} := by decide +kernel
  have hxd : x.val \ y.val = {label 6} := by decide +kernel
  have hyd : y.val \ x.val = {label 4} := by decide +kernel
  constructor
  · intro hg
    have hy := MulAction.mem_stabilizer_iff.mp hg
    have hf5 : (g : M23) • label 5 = label 5 := by
      have h : (g : M23) • (x.val ∩ y.val) = x.val ∩ y.val := by
        rw [Finset.smul_finset_inter, hx, hy]
      simpa only [hxy, Finset.smul_finset_singleton, Finset.singleton_inj] using h
    have hf6 : (g : M23) • label 6 = label 6 := by
      have h : (g : M23) • (x.val \ y.val) = x.val \ y.val := by
        rw [Finset.smul_finset_sdiff, hx, hy]
      simpa only [hxd, Finset.smul_finset_singleton, Finset.singleton_inj] using h
    have hf4 : (g : M23) • label 4 = label 4 := by
      have h : (g : M23) • (y.val \ x.val) = y.val \ x.val := by
        rw [Finset.smul_finset_sdiff, hx, hy]
      simpa only [hyd, Finset.smul_finset_singleton, Finset.singleton_inj] using h
    exact ⟨(mem_pointwisePairStabilizer g).mpr ⟨hf5, hf6⟩, Subtype.ext hf4⟩
  · rintro ⟨hg, hp⟩
    have hf5 := ((mem_pointwisePairStabilizer g).mp hg).1
    have hf4 : (g : M23) • label 4 = label 4 := congrArg Subtype.val hp
    apply MulAction.mem_stabilizer_iff.mpr
    simp only [y, Finset.smul_finset_insert, Finset.smul_finset_singleton, hf4, hf5]

/-- Setwise heptad stabilization is precisely line stabilization after deleting
an invariant pair. -/
theorem mem_heptad_stabilizer_iff_line_fixed {P B : Finset (Fin 23)}
    (hPB : P ⊆ B) (hB : B ∈ m23Blocks) (g : MulAction.stabilizer M23 P) :
    (g : M23) ∈ MulAction.stabilizer M23 B ↔
      lineAction P g ⟨B \ P, mem_pairLines.mpr ⟨B, hB, hPB, rfl⟩⟩ =
        ⟨B \ P, mem_pairLines.mpr ⟨B, hB, hPB, rfl⟩⟩ := by
  have hp := MulAction.mem_stabilizer_iff.mp g.property
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hb
    apply Subtype.ext
    change (g : M23) • (B \ P) = B \ P
    rw [Finset.smul_finset_sdiff, hp, hb]
  · intro h
    have hl : (g : M23) • (B \ P) = B \ P := congrArg Subtype.val h
    calc
      (g : M23) • B = (g : M23) • (P ∪ (B \ P)) := by rw [heptad_recover hPB]
      _ = P ∪ (B \ P) := by rw [Finset.smul_finset_union, hp, hl]
      _ = B := heptad_recover hPB

theorem mem_heptadStabilizer_iff (g : pairStabilizer) :
    (g : M23) ∈ heptadStabilizer ↔ lineAction x.val g omegaLine = omegaLine :=
  mem_heptad_stabilizer_iff_line_fixed
    (x_subset_lambda.trans lambda_subset_omega) omega_mem g

/-- The two subgroup descriptions agree before any choice of coordinates. -/
theorem adjacent_stabilizer_comap :
    (MulAction.stabilizer M23 y.val).comap pairStabilizer.subtype =
      pointwisePairStabilizer ⊓
        (MulAction.stabilizer (Equiv.Perm (pairComplement x.val)) adjacentPoint).comap
          (complementAction x.val) := by
  ext g
  exact mem_adjacent_stabilizer_iff g

theorem heptad_stabilizer_comap :
    heptadStabilizer.comap pairStabilizer.subtype =
      (MulAction.stabilizer (Equiv.Perm (pairLines x.val)) omegaLine).comap
        (lineAction x.val) := by
  ext g
  exact mem_heptadStabilizer_iff g

/-- Mapping the internal parabolic back to M23 gives the intersection of the
stabilizers of the two adjacent vertices. -/
theorem adjacent_stabilizer_map :
    (pointwisePairStabilizer ⊓
      (MulAction.stabilizer (Equiv.Perm (pairComplement x.val)) adjacentPoint).comap
        (complementAction x.val)).map pairStabilizer.subtype =
      pairStabilizer ⊓ MulAction.stabilizer M23 y.val := by
  rw [← adjacent_stabilizer_comap, Subgroup.map_comap_eq, Subgroup.range_subtype]

/-- Mapping the line stabilizer back to M23 gives the pair/heptad intersection. -/
theorem heptad_stabilizer_map :
    ((MulAction.stabilizer (Equiv.Perm (pairLines x.val)) omegaLine).comap
      (lineAction x.val)).map pairStabilizer.subtype =
      pairStabilizer ⊓ heptadStabilizer := by
  rw [← heptad_stabilizer_comap, Subgroup.map_comap_eq, Subgroup.range_subtype]

/-- The action on the complementary 21 points is faithful. A heptad containing
exactly one deleted point rules out a permutation supported on the pair. -/
theorem complementAction_injective : Function.Injective (complementAction x.val) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hfix (a : Fin 23) (ha : a ∉ x.val) : (g : M23) • a = a := by
    let a' : pairComplement x.val := ⟨a, by simp [pairComplement, ha]⟩
    exact congrArg Subtype.val (Equiv.congr_fun hg a')
  let B := m23BlockAt 13
  let S : Finset (Fin 23) := {1, 2, 6, 15}
  have hS : S.card = 4 := by decide +kernel
  have hB : B ∈ m23Blocks := Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  have hSB : S ⊆ B := by decide +kernel
  have hSP : ∀ a ∈ S, a ∉ x.val := by decide +kernel
  have hSfix : (g : M23) ∈ MulAction.stabilizer M23 S := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    rw [hfix a (hSP a ha)]
    exact ha
  have hBfix := MulAction.mem_stabilizer_iff.mp
    (four_stabilizer_le_heptad_stabilizer hS hB hSB hSfix)
  have hxfix := MulAction.mem_stabilizer_iff.mp g.property
  have hBx : B ∩ x.val = {label 5} := by decide +kernel
  have hxB : x.val \ B = {label 6} := by decide +kernel
  have hf5 : (g : M23) • label 5 = label 5 := by
    have h : (g : M23) • (B ∩ x.val) = B ∩ x.val := by
      rw [Finset.smul_finset_inter, hBfix, hxfix]
    simpa only [hBx, Finset.smul_finset_singleton, Finset.singleton_inj] using h
  have hf6 : (g : M23) • label 6 = label 6 := by
    have h : (g : M23) • (x.val \ B) = x.val \ B := by
      rw [Finset.smul_finset_sdiff, hBfix, hxfix]
    simpa only [hxB, Finset.smul_finset_singleton, Finset.singleton_inj] using h
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro a
  change (g : M23) • a = a
  by_cases ha : a ∈ x.val
  · simp only [x, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hf5
    · exact hf6
  · exact hfix a ha

end Sporadic.Mathieu.M23Geometry
