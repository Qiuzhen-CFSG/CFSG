module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Edges
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Faithfulness of the Mathieu source coset action from local geometry

Every nontrivial normal subgroup of the row normalizer contains its
self-centralizing natural module: the full linear action is transitive on
nonzero vectors. A nontrivial ambient core would therefore contain the row.
The row has order sixteen while its kernel on a source line has order eight,
so some row element interchanges the other two points. Conjugating by a line
reversal contradicts containment of the core in the point stabilizer.

Thus faithfulness holds in the normalizer-generated subgroup as well as the
original ambient group, with no simplicity hypothesis. This supplies the
induction-system input in Aschbacher, *Sporadic Groups* (1994), 41.1 and 41.4,
printed pp.219–222. Global ambient generation is a separate obligation.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer PlaneTensor PlaneCensus GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

private theorem nonzero_transitive {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ f : V ≃ₗ[ZMod 2] V, f a = b := by
  let ea := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V a ha
  let eb := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V b hb
  obtain ⟨f, hf⟩ := Submodule.exists_linearEquiv_restrict_eq (ea.symm.trans eb)
  refine ⟨f, ?_⟩
  have h := hf (ea 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ea, eb] using h.symm

omit [Finite G] in
include D in
/-- The full natural row action is transitive on the nonidentity elements
of the literal row group. -/
theorem row_nonidentity_transitive (a b : F.row) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ n : rowNormalizer F, F.row.normalizerMonoidHom n a = b := by
  let c := rowCoordinates F
  have ha0 : (c a).toAdd ≠ 0 := fun h => ha (c.map_eq_one_iff.mp h)
  have hb0 : (c b).toAdd ≠ 0 := fun h => hb (c.map_eq_one_iff.mp h)
  obtain ⟨f, hf⟩ := nonzero_transitive (c a).toAdd (c b).toAdd ha0 hb0
  obtain ⟨n, hn⟩ := rowAction_surjective F D f
  refine ⟨n, c.injective (Multiplicative.toAdd.injective ?_)⟩
  rw [← rowAction_coordinates F D, hn]
  exact hf

omit [Finite G] in
include D in
/-- Every nontrivial normal subgroup of the full row normalizer contains
its self-centralizing natural module. -/
theorem row_le_normal_of_ne_bot (N : Subgroup (rowNormalizer F)) [N.Normal] (hN : N ≠ ⊥) :
    F.row.subgroupOf (rowNormalizer F) ≤ N := by
  let A := F.row.subgroupOf (rowNormalizer F)
  have hi : ¬ Disjoint N A := by
    intro hd
    have hc : N ≤ Subgroup.centralizer (A : Set (rowNormalizer F)) :=
      commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
    have hnA : N ≤ A := by
      intro n hn
      change (n : G) ∈ F.row
      rw [← row_centralizer_eq F]
      apply mem_centralizer_iff.mpr
      intro a ha
      exact congrArg Subtype.val (mem_centralizer_iff.mp (hc hn)
        ⟨a, F.row.le_normalizer ha⟩ ha)
    exact hN (bot_unique fun n hn => disjoint_def.mp hd hn (hnA hn))
  rw [disjoint_def] at hi
  push Not at hi
  obtain ⟨a, haN, haA, ha1⟩ := hi
  intro b hb
  by_cases hb1 : b = 1
  · simpa only [hb1] using N.one_mem
  obtain ⟨n, he⟩ := row_nonidentity_transitive F D
    ⟨a, haA⟩ ⟨b, hb⟩ (by
      intro h
      exact ha1 (Subtype.ext (congrArg (fun x : F.row => (x : G)) h))) (by
      intro h
      exact hb1 (Subtype.ext (congrArg (fun x : F.row => (x : G)) h)))
  have hnN := (inferInstance : N.Normal).conj_mem a haN n
  have he' : n * a * n⁻¹ = b := Subtype.ext (congrArg (fun x : F.row => (x : G)) he)
  exact he' ▸ hnN

private theorem perm_three_moves_after_swap : ∀ p : Equiv.Perm (Fin 3),
    p 0 = 0 → p ≠ 1 → ((Equiv.swap 0 1 * p * (Equiv.swap 0 1)⁻¹ : Equiv.Perm (Fin 3))) 0 ≠ 0 := by decide

include D in
/-- The literal row-normalizer coset action is faithful already from the
local source data; ambient simplicity and global generation are unnecessary. -/
theorem row_normalizer_core : (rowNormalizer F).normalCore = ⊥ := by
  let K := (rowNormalizer F).normalCore
  by_contra hK
  have hK' : K.subgroupOf (rowNormalizer F) ≠ ⊥ := by
    intro he
    apply hK
    apply bot_unique
    intro k hk
    have hk' : (⟨k, (rowNormalizer F).normalCore_le hk⟩ : rowNormalizer F) ∈
        K.subgroupOf (rowNormalizer F) := hk
    rw [he] at hk'
    exact congrArg Subtype.val hk'
  have hA := row_le_normal_of_ne_bot F D (K.subgroupOf (rowNormalizer F)) hK'
  have hnotle : ¬ F.row ≤ F.plane := by
    intro hle
    have hh := SourceNormalizer.row_plane_card F
    rw [inf_eq_left.mpr hle, row_card] at hh
    omega
  obtain ⟨a, har, hap⟩ := SetLike.not_le_iff_exists.mp hnotle
  let n : planeNormalizer F := inclusion (row_le_line_normalizer F) ⟨a, har⟩
  have hnK : a ∈ K := hA (x := ⟨a, F.row.le_normalizer har⟩) har
  have hn0 : lineAction F D n 0 = 0 :=
    (lineAction_fix_iff F D n).mpr (F.row.le_normalizer har)
  have hne : lineAction F D n ≠ 1 := fun h => hap ((row_line_kernel_iff F D ⟨a, har⟩).mp h)
  let t := lineSwap F D
  have hconj : (t : G) * a * (t : G)⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem _ hnK t
  have hfix := (lineAction_fix_iff F D (t * n * t⁻¹)).mpr
    ((rowNormalizer F).normalCore_le hconj)
  rw [map_mul, map_mul, map_inv, lineSwap_action] at hfix
  exact perm_three_moves_after_swap _ hn0 hne hfix

include D in
/-- Faithfulness in the exact source graph, valid in the induction overgroup. -/
theorem graph_faithful_of_localData (g : G) (hg : ∀ a : Point F, g • a = a) : g = 1 :=
  GraphUniquenessSystem.Cosets.faithful _ (row_normalizer_core F D) g hg

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
