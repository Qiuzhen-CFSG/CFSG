module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.FiveSupportFamily
public import Theory.GroupTheory.PPerfectHom

/-!
# Two-perfect actors on a small canonical support family

Ambient conjugation permutes the actual canonical quintic factors.
When this family has at most two members, a two-perfect subgroup fixes
each member, because the permutation group is a two-group.

Source: Aschbacher–Smith D.2.12 and the quintic branch of 14.5.11,
printed pp.183–184 and1015–1016, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G] [Group V]
  [MulDistribMulAction G V]

private theorem perm_twoGroup_of_card_le_two {I : Type*} [Finite I]
    (hc : Nat.card I ≤ 2) : IsPGroup 2 (Equiv.Perm I) := by
  have hcard : Nat.card (Equiv.Perm I) ∣ 2 := by
    rw [Nat.card_perm]
    have hi : Nat.card I = 0 ∨ Nat.card I = 1 ∨ Nat.card I = 2 := by omega
    rcases hi with hi | hi | hi <;> simp [hi]
  exact IsPGroup.of_card_dvd_pow (n := 1) hcard

/-- Every actual canonical factor is normalized by the two-perfect actor. -/
theorem smallSupportFactors_twoPerfect_normalizes
    (hcard : Nat.card (smallSupportFactors G V 2) ≤ 2)
    (X : Subgroup G) (hX : IsPPerfect 2 X)
    (C : Subgroup G) (hC : C ∈ smallSupportFactors G V 2) :
    X ≤ normalizer (C : Set G) := by
  let I := smallSupportFactors G V 2
  let f : X →* Equiv.Perm I := {
    toFun := fun x => smallSupportFactors_conjEquiv 2 (x : G)
    map_one' := by
      apply Equiv.ext
      intro c
      exact Subtype.ext (conjBy_one c.val)
    map_mul' := by
      intro x y
      apply Equiv.ext
      intro c
      exact Subtype.ext (conjBy_mul c.val x y)
  }
  have hf := hX.hom_eq_one_of_isPGroup (perm_twoGroup_of_card_le_two hcard) f
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact congrArg (fun a : X →* Equiv.Perm I => (a ⟨x,hx⟩ ⟨C,hC⟩).val) hf

end CFSG.Quasithin.ChapterD
