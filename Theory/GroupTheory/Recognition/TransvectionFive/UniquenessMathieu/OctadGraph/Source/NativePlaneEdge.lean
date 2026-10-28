module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativePlane
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.System

/-!
# Detecting and aligning an edge in the native sextet action

The fifteen octads of the marked sextet correspond to pairs of its six
hexacode columns. A common point stabilizer of order 1536 has image of order
eight in S₆. The small pair-action calculation forces the pairs to be
disjoint, hence the actual octads are adjacent. Plane edge transitivity then
supplies a correction fixing the first octad and aligning the second.

This supplies the native geometric step of Aschbacher, *Sporadic Groups*
(1994), 41.4, p.222. The consumer in `AlignPlaneEdge` transports the literal
source plane–edge intersection, rather than identifying abstract subgroups.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph.NativePlaneEdge
open Sporadic.Mathieu.M24ChapterHStabilizers
open BinaryPermutation.SixPairsQuadratic
open Atlas.Codes MathieuCode

@[expose] def pairFix (s : Pair) : Subgroup (Equiv.Perm (Fin 6)) :=
  (MulAction.stabilizer (Equiv.Perm Pair) s).comap pairHom

@[simp] theorem mem_pairFix (p : Equiv.Perm (Fin 6)) (s : Pair) :
    p ∈ pairFix s ↔ pairPerm p s = s := Iff.rfl

theorem sextet_mem_first (g : sextetStabilizer standardSextet) :
    (g : M24) ∈ octadStabilizer first ↔
      SextetCore.columnHom g ∈ pairFix CommonPlane.basePair := by
  rw [NativePlane.first_eq_standardOctad, NativePlane.sextet_mem_octad_iff]
  change _ • CommonPlane.basePair.val = CommonPlane.basePair.val ↔ _
  rw [mem_pairFix, Subtype.ext_iff]
  simp only [pairPerm,Finset.smul_finset_def,Finset.map_eq_image]
  rfl

/-- In the six-column action, the common fixer has order eight precisely
when the second pair is disjoint from the marked pair. -/
theorem pairFix_inter_card_eight (s : Pair)
    (hc : Nat.card ↥(pairFix CommonPlane.basePair ⊓ pairFix s) = 8) :
    Disjoint CommonPlane.basePair.val s.val := by
  change Nat.card {p : Equiv.Perm (Fin 6) //
    pairPerm p CommonPlane.basePair = CommonPlane.basePair ∧ pairPerm p s = s} = 8 at hc
  rw [Nat.card_eq_fintype_card] at hc
  exact (by decide +kernel : ∀ s : Pair,
    Fintype.card {p : Equiv.Perm (Fin 6) //
      pairPerm p CommonPlane.basePair = CommonPlane.basePair ∧ pairPerm p s = s} = 8 →
      Disjoint CommonPlane.basePair.val s.val) s hc

/-- The column of an actual point, in the native hexacode coordinates. -/
@[expose] def column (x : Fin 24) : Fin 6 := hexIndexEquiv (atlasPointEquiv.symm x).1

@[simp] theorem column_smul (g : sextetStabilizer standardSextet) (x : Fin 24) :
    column ((g : M24) • x) = SextetCore.columnHom g (column x) := by
  obtain ⟨⟨i,k⟩,rfl⟩ := atlasPointEquiv.surjective x
  simp only [column, Equiv.symm_apply_apply]
  change hexIndexEquiv (atlasPointEquiv.symm (g.val.val (atlasPointEquiv (i,k)))).1 = _
  exact (SextetCore.columnHom_apply g i k).symm

theorem first_coordinates (x : Fin 24) : x ∈ first.val ↔ column x ∈ CommonPlane.basePair.val := by
  rw [NativePlane.first_eq_standardOctad]
  obtain ⟨⟨i,k⟩,rfl⟩ := atlasPointEquiv.surjective x
  simpa only [column, Equiv.symm_apply_apply] using CommonPlane.octad_coordinates i k

theorem smul_first_coordinates (g : sextetStabilizer standardSextet) (x : Fin 24) :
    x ∈ ((g : M24) • first).val ↔
      column x ∈ (pairPerm (SextetCore.columnHom g) CommonPlane.basePair).val := by
  change x ∈ (g : M24) • first.val ↔ _
  rw [← Finset.inv_smul_mem_iff, first_coordinates]
  change column (((g⁻¹ : sextetStabilizer standardSextet) : M24) • x) ∈ _ ↔ _
  rw [column_smul, map_inv]
  change (SextetCore.columnHom g)⁻¹ • column x ∈ CommonPlane.basePair.val ↔ _
  rw [Finset.inv_smul_mem_iff]
  simp only [pairPerm,Finset.smul_finset_def,Finset.map_eq_image]
  rfl

theorem adjacent_of_disjoint_pairs (g : sextetStabilizer standardSextet)
    (hd : Disjoint CommonPlane.basePair.val
      (pairPerm (SextetCore.columnHom g) CommonPlane.basePair).val) :
    graph.Adj first ((g : M24) • first) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact Finset.disjoint_left.mp hd ((first_coordinates x).mp hx)
    ((smul_first_coordinates g x).mp hy)

theorem mem_pairFix_image (p q : Equiv.Perm (Fin 6)) (s : Pair) :
    p ∈ pairFix (pairPerm q s) ↔ q⁻¹ * p * q ∈ pairFix s := by
  simp only [mem_pairFix]
  change pairHom p (pairHom q s) = pairHom q s ↔ pairHom (q⁻¹ * p * q) s = s
  rw [map_mul,map_mul,map_inv]
  change _ ↔ (pairHom q).symm (pairHom p (pairHom q s)) = s
  rw [Equiv.symm_apply_eq]

theorem sextet_mem_smul_first (g n : sextetStabilizer standardSextet) :
    (n : M24) ∈ octadStabilizer ((g : M24) • first) ↔
      SextetCore.columnHom n ∈ pairFix (pairPerm (SextetCore.columnHom g) CommonPlane.basePair) := by
  rw [mem_pairFix_image, ← map_inv, ← map_mul, ← map_mul, ← sextet_mem_first]
  rw [← stabilizer_octad, ← stabilizer_octad]
  change (n : M24) • ((g : M24) • first) = (g : M24) • first ↔
    ((g : M24)⁻¹ * (n : M24) * (g : M24)) • first = first
  rw [mul_smul,mul_smul,inv_smul_eq_iff]

theorem adjacent_of_fixer_card (g : sextetStabilizer standardSextet)
    (hc : Nat.card ((octadStabilizer first ⊓ octadStabilizer ((g : M24) • first)).subgroupOf
      (sextetStabilizer standardSextet)) = 1536) :
    graph.Adj first ((g : M24) • first) := by
  let K := pairFix CommonPlane.basePair ⊓
    pairFix (pairPerm (SextetCore.columnHom g) CommonPlane.basePair)
  have he : (octadStabilizer first ⊓ octadStabilizer ((g : M24) • first)).subgroupOf
      (sextetStabilizer standardSextet) = K.comap SextetCore.columnHom := by
    ext n
    exact and_congr (sextet_mem_first n) (sextet_mem_smul_first g n)
  rw [he] at hc
  have hi := (K.comap SextetCore.columnHom).card_mul_index
  rw [hc,index_comap_of_surjective _ SextetCore.columnHom_surjective,
    SextetCore.stabilizer_card] at hi
  have hk := K.card_mul_index
  have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    norm_num [Nat.card_perm,Fintype.card_perm,Nat.factorial]
  rw [h720] at hk
  have h90 : K.index = 90 := by omega
  rw [h90] at hk
  apply adjacent_of_disjoint_pairs
  apply pairFix_inter_card_eight
  change Nat.card K = 8
  omega

/-- Correct the second endpoint inside the actual point–plane stabilizer. -/
theorem exists_edge_correction (g : sextetStabilizer standardSextet)
    (hc : Nat.card ((octadStabilizer first ⊓ octadStabilizer ((g : M24) • first)).subgroupOf
      (sextetStabilizer standardSextet)) = 1536) :
    ∃ k : sextetStabilizer standardSextet,
      (k : M24) • first = first ∧ (k : M24) • ((g : M24) • first) = second := by
  have hfirst := standardTrio_on_standardSextet first first_on_standardTrio
  have hg := onPlane_smul (g : M24) hfirst
  have hs : (g : M24) • standardSextet = standardSextet := Sextet.ext g.property
  rw [hs] at hg
  obtain ⟨k,hkx,hky⟩ := plane_edge_transitive (adjacent_of_fixer_card g hc) hfirst hg
  refine ⟨k⁻¹,?_,?_⟩
  · change (k : M24)⁻¹ • first = first
    rw [inv_smul_eq_iff,hkx]
  · change (k : M24)⁻¹ • ((g : M24) • first) = second
    rw [inv_smul_eq_iff,hky]

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph.NativePlaneEdge
