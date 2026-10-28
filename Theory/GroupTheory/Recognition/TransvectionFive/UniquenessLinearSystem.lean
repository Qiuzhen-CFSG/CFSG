module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearModel
import Mathlib.Tactic.FinCases

/-!
# Construction of the binary five-space uniqueness system

The complete graph on nonzero vectors, the stabilizer of the coordinate
three-space, and the edge joining the first two basis vectors form an actual
uniqueness system. Pair transport proves global and local generation. For
vertex-stabilizer generation, a point in the fixed plane is reached within
its stabilizer; a point outside the plane is reached by extending an independent
three-vector frame while fixing both endpoints of the chosen edge.

Thus all three generation identities and faithfulness are proved for the
literal matrix group. The plane cycle-base theorem applies without any extra
model premise. Source: Aschbacher, *Sporadic Groups* (1994), Example 38.4,
pp.206–207, and Lemma 41.5, p.222.
-/

public noncomputable section
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open BinaryLinear.TransvectionFiveLocal Subgroup GraphUniquenessSystem

private theorem basisPoint_ne {i j : Fin 5} (hij : i ≠ j) : basisPoint i ≠ basisPoint j := by
  intro he
  have hh := congrArg (fun v : Point => v.val i) he
  simp [basisPoint, hij] at hh

private theorem pair_transport (a b c d : Point) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : SL, g • a = c ∧ g • b = d := by
  obtain ⟨f, hf, hf'⟩ := BinaryLinear.exists_linearEquiv_pair a.val b.val c.val d.val
    a.property b.property c.property d.property
    (fun he => hab (Subtype.ext he)) (fun he => hcd (Subtype.ext he))
  refine ⟨linearEquiv.symm f, Subtype.ext ?_, Subtype.ext ?_⟩
  · simpa using hf
  · simpa using hf'

private theorem pair_independent : LinearIndependent (ZMod 2)
    ![(basisPoint 0).val, (basisPoint 1).val] := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h0 := congrFun hf 0
  have h1 := congrFun hf 1
  fin_cases i
  · simpa [Fin.sum_univ_two, basisPoint] using h0
  · simpa [Fin.sum_univ_two, basisPoint] using h1

private theorem pair_span_le_plane :
    Submodule.span (ZMod 2) (Set.range ![(basisPoint 0).val, (basisPoint 1).val]) ≤
      planeSpace := by
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  fin_cases i <;> exact basisPoint_mem_plane (by simp)

private theorem third_not_mem_pair_span : (basisPoint 2).val ∉
    Submodule.span (ZMod 2) (Set.range ![(basisPoint 0).val, (basisPoint 1).val]) := by
  intro h
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at h
  obtain ⟨a, b, he⟩ := h
  have hh := congrFun he 2
  simp [basisPoint] at hh

private theorem edge_fixer_transport (a : Point) (ha : a.val ∉ planeSpace) :
    ∃ g : SL, g • basisPoint 0 = basisPoint 0 ∧
      g • basisPoint 1 = basisPoint 1 ∧ g • basisPoint 2 = a := by
  have ha' : a.val ∉ Submodule.span (ZMod 2)
      (Set.range ![(basisPoint 0).val, (basisPoint 1).val]) :=
    fun h => ha (pair_span_le_plane h)
  have hs := pair_independent.finCons third_not_mem_pair_span
  have ht := pair_independent.finCons ha'
  let f := hs.linearCombinationEquiv.symm ≪≫ₗ ht.linearCombinationEquiv
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have he (i : Fin 3) :
      g (![(basisPoint 2).val, (basisPoint 0).val, (basisPoint 1).val] i) =
        ![a.val, (basisPoint 0).val, (basisPoint 1).val] i := by
    have hh := hg (hs.linearCombinationEquiv (Finsupp.single i 1))
    simpa [f] using hh.symm
  refine ⟨linearEquiv.symm g, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · simpa using he 1
  · simpa using he 2
  · simpa using he 0

/-- A subgroup containing a relative point stabilizer is determined by its orbit. -/
private theorem le_of_orbit_cover {A P : Type*} [Group A] [MulAction A P]
    (L K : Subgroup A) (p : P) (hKL : K ≤ L)
    (hfix : ∀ g ∈ L, g • p = p → g ∈ K)
    (hcover : ∀ g ∈ L, ∃ k ∈ K, k • p = g • p) : L ≤ K := by
  intro g hg
  obtain ⟨k, hk, he⟩ := hcover g hg
  have hmem : k⁻¹ * g ∈ K := hfix _ (L.mul_mem (L.inv_mem (hKL hk)) hg) (by
    rw [mul_smul, ← he, inv_smul_smul])
  simpa using K.mul_mem hk hmem

private theorem plane_smul_mem {g : SL} (hg : g ∈ planeGroup) {v : Point}
    (hv : v.val ∈ planeSpace) : (g • v : Point).val ∈ planeSpace :=
  (hg v.val).mpr hv

private theorem generation : planeGroup ⊔ MulAction.stabilizer SL (basisPoint 0) = ⊤ := by
  let K := planeGroup ⊔ MulAction.stabilizer SL (basisPoint 0)
  have hxy := basisPoint_ne (by decide : (0 : Fin 5) ≠ 1)
  obtain ⟨t, htx, hty⟩ := exists_plane_pair (basisPoint 1) (basisPoint 0)
    (basisPoint_mem_plane (by simp)) (basisPoint_mem_plane (by simp)) hxy.symm
  apply top_unique
  apply le_of_orbit_cover ⊤ K (basisPoint 0) le_top
  · intro g _ hg
    exact mem_sup_right hg
  · intro g _
    by_cases ha : g • basisPoint 0 = basisPoint 0
    · exact ⟨1, K.one_mem, (one_smul _ _).trans ha.symm⟩
    obtain ⟨m, hmx, hmy⟩ := pair_transport (basisPoint 0) (basisPoint 1)
      (basisPoint 0) (g • basisPoint 0) hxy (Ne.symm ha)
    refine ⟨m * t, K.mul_mem (mem_sup_right hmx) (mem_sup_left t.property), ?_⟩
    rw [mul_smul, htx, hmy]

private theorem vertex_generation :
    edgeFixer SL (basisPoint 0) (basisPoint 1) ⊔
      (planeGroup ⊓ MulAction.stabilizer SL (basisPoint 0)) =
        MulAction.stabilizer SL (basisPoint 0) := by
  let M := MulAction.stabilizer SL (basisPoint 0)
  let B := edgeFixer SL (basisPoint 0) (basisPoint 1)
  let K := B ⊔ (planeGroup ⊓ M)
  have hKM : K ≤ M := sup_le inf_le_left inf_le_right
  have hxy := basisPoint_ne (by decide : (0 : Fin 5) ≠ 1)
  have hxz := basisPoint_ne (by decide : (0 : Fin 5) ≠ 2)
  apply le_antisymm hKM
  apply le_of_orbit_cover M K (basisPoint 1) hKM
  · intro g hg hgy
    exact mem_sup_left ⟨hg, hgy⟩
  · intro g hg
    have hgx : g • basisPoint 0 = basisPoint 0 := hg
    have hga : basisPoint 0 ≠ g • basisPoint 1 := by
      intro he
      exact hxy (MulAction.injective g (hgx.trans he))
    by_cases ha : (g • basisPoint 1 : Point).val ∈ planeSpace
    · obtain ⟨h, hhx, hhy⟩ := exists_plane_pair (basisPoint 0) (g • basisPoint 1)
        (basisPoint_mem_plane (by simp)) ha hga
      exact ⟨h, mem_sup_right ⟨h.property, hhx⟩, hhy⟩
    · obtain ⟨b, hbx, hby, hba⟩ := edge_fixer_transport (g • basisPoint 1) ha
      obtain ⟨h, hhx, hhz⟩ := exists_plane_pair (basisPoint 0) (basisPoint 2)
        (basisPoint_mem_plane (by simp)) (basisPoint_mem_plane (by simp)) hxz
      refine ⟨b * h, K.mul_mem (mem_sup_left ⟨hbx, hby⟩)
        (mem_sup_right ⟨h.property, hhx⟩), ?_⟩
      rw [mul_smul, hhz, hba]

private theorem local_generation :
    (planeGroup ⊓ edgeStabilizer SL (basisPoint 0) (basisPoint 1)) ⊔
      (planeGroup ⊓ MulAction.stabilizer SL (basisPoint 0)) = planeGroup := by
  let K := (planeGroup ⊓ edgeStabilizer SL (basisPoint 0) (basisPoint 1)) ⊔
      (planeGroup ⊓ MulAction.stabilizer SL (basisPoint 0))
  have hKH : K ≤ planeGroup := sup_le inf_le_left inf_le_left
  have hxy := basisPoint_ne (by decide : (0 : Fin 5) ≠ 1)
  obtain ⟨t, htx, hty⟩ := exists_plane_pair (basisPoint 1) (basisPoint 0)
    (basisPoint_mem_plane (by simp)) (basisPoint_mem_plane (by simp)) hxy.symm
  apply le_antisymm hKH
  apply le_of_orbit_cover planeGroup K (basisPoint 0) hKH
  · intro g hg hfix
    exact mem_sup_right ⟨hg, hfix⟩
  · intro g hg
    by_cases ha : g • basisPoint 0 = basisPoint 0
    · exact ⟨1, K.one_mem, (one_smul _ _).trans ha.symm⟩
    obtain ⟨m, hmx, hmy⟩ := exists_plane_pair (basisPoint 0) (g • basisPoint 0)
      (basisPoint_mem_plane (by simp))
      (plane_smul_mem hg (basisPoint_mem_plane (by simp))) (Ne.symm ha)
    refine ⟨m * t, K.mul_mem (mem_sup_right ⟨m.property, hmx⟩)
      (mem_sup_left ⟨t.property, Or.inr ⟨htx, hty⟩⟩), ?_⟩
    rw [mul_smul, htx, hmy]

/-- The actual SL₅(2) uniqueness system on nonzero binary vectors. -/
def nativeSystem : NativeSystem where
  system := {
    graph := ⊤
    H := planeGroup
    x := basisPoint 0
    y := basisPoint 1
    adjacent := basisPoint_ne (by decide)
    preserves := fun g _ _ hab => fun he => hab (MulAction.injective g he)
    faithful := by
      intro g hg
      apply linearEquiv.injective
      apply LinearEquiv.ext
      intro v
      by_cases hv : v = 0
      · simp [hv]
      · simpa using congrArg Subtype.val (hg ⟨v, hv⟩)
    vertex_transitive := by
      intro a
      by_cases ha : a = basisPoint 0
      · exact ⟨1, by rw [ha, one_smul]⟩
      obtain ⟨g, hg, _⟩ := pair_transport (basisPoint 0) a a (basisPoint 0) (Ne.symm ha) ha
      exact ⟨g, hg⟩
    edge_transitive := by
      intro a b hab
      obtain ⟨g, hg⟩ := pair_transport (basisPoint 0) (basisPoint 1) a b
        (basisPoint_ne (by decide)) hab
      exact ⟨g, Or.inl hg⟩
    local_orbit := by
      obtain ⟨t, ht, _⟩ := exists_plane_pair (basisPoint 1) (basisPoint 0)
        (basisPoint_mem_plane (by simp)) (basisPoint_mem_plane (by simp))
        (basisPoint_ne (by decide))
      exact ⟨t, ht⟩
    generate := generation
    vertex_generate := vertex_generation
    local_generate := local_generation }
  graph_eq := rfl
  local_eq := rfl
  point_eq := rfl
  neighbor_eq := rfl

/-- The concrete model satisfies the target base condition, with no remaining input. -/
theorem nativeSystem_isBase : nativeSystem.system.IsBase := nativeSystem.isBase
end Theory.GroupTheory.TransvectionFive.UniquenessLinear
