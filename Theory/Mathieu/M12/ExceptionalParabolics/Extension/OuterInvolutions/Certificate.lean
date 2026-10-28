module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Coordinates
/-!
# Checked outer-involution words in the Aut(M₁₂) Sylow subgroup

The actual overlap has 128 elements. Its involutions whose marked block moves
are precisely eight indexed words. Each is conjugate to the original outer
generator by a displayed word of length at most eighteen. Both exhaustive
coverage and the eight identities are checked by the Lean kernel on the
literal degree-24 permutations; no search output is trusted.

The marked-block hypothesis is discharged by the index-two inner subgroup in
the parent module. Source: Aschbacher–Smith H.11.1 and K.4.2; the imported
carrier retains the ATLAS M12d2G1-p24B0 attribution.
-/
public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OuterInvolutions
open Subgroup OverlapExtensions
set_option maxRecDepth 10000
@[expose] def seed : Carrier := ⟨generatorA, subset_closure (by simp)⟩
private def other : Carrier := ⟨generatorB, subset_closure (by simp)⟩
private def generators : Fin 3 → Carrier := ![seed, other, other⁻¹]
private def words : Fin 8 → List (Fin 3) := ![
  [0,1,0,2,0,1,0,1,0,2,0,1],
  [0,1,0,1,0,2,0,2,0,1,0,1,0,1,0,1],
  [0,1,0,2,0,1,0,1,0,1,0,1,0,2,0,1,0,2],
  [0,1,0,1,0,2,0,1,0,2],
  [1,0,2,0,1,0,1,0,1,0,2,0,1,0,1],
  [2,0,1,0,2,0,2,0,1,0,2,0,1,0,1,0,1],
  [2,0,2,0,1,0,1,0,2,0,2,0,2],
  [0,1,0,1,0,2,0,2,0,2,0,1,0,2,0,1]]
private def conjugator (k : Fin 8) : Carrier := FiniteWords.evaluate generators (words k)
private def indices : Fin 8 → Fin 128 := ![2,12,14,45,70,103,113,127]
private def perm (i : Fin 128) : Equiv.Perm (Fin 24) :=
  FiniteWords.evaluate Overlap.generatorPerm (Data.overlapWords i)
private def conjugatorPerm (i : Fin 8) : Equiv.Perm (Fin 24) :=
  FiniteWords.evaluate ![generatorA,generatorB,generatorB⁻¹] (words i)
private theorem coverage : ∀ i : Fin 128,
    perm i ^ 2 = 1 →
    (∃ j : Fin 12, generatorA (perm i (blockLabel 0)) = blockLabel j) →
    ∃ k : Fin 8, i = indices k := by
  decide +kernel
private theorem conjugacy : ∀ k : Fin 8,
    conjugatorPerm k * generatorA * (conjugatorPerm k)⁻¹ =
      perm (indices k) := by
  decide +kernel
private theorem conjugator_val (i : Fin 8) : (conjugator i).val = conjugatorPerm i := by
  have hg : (fun j => group.subtype (generators j)) =
      ![generatorA,generatorB,generatorB⁻¹] := by
    funext j
    fin_cases j <;> rfl
  have h := FiniteWords.map_evaluate group.subtype generators (words i)
  rw [hg] at h
  simpa only [conjugator, conjugatorPerm, Subgroup.subtype_apply] using h
theorem sylow_fusion_of_marker (i : Fin 128)
    (hp : (Overlap.element i : Carrier) ^ 2 = 1)
    (hb : ∃ j : Fin 12, generatorA ((Overlap.element i).val.val (blockLabel 0)) = blockLabel j) :
    IsConj seed (Overlap.element i : Carrier) := by
  have hpp : perm i ^ 2 = 1 := by
    have hh := congrArg Subtype.val hp
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, Overlap.element_val, perm] using hh
  have hbb : ∃ j : Fin 12, generatorA (perm i (blockLabel 0)) = blockLabel j := by
    simpa only [Overlap.element_val, perm] using hb
  obtain ⟨k, rfl⟩ := coverage i hpp hbb
  apply isConj_iff.mpr
  refine ⟨conjugator k, ?_⟩
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, conjugator_val, seed,
    Overlap.element_val, perm] using conjugacy k

end Sporadic.Mathieu.M12ExceptionalExtension.OuterInvolutions
