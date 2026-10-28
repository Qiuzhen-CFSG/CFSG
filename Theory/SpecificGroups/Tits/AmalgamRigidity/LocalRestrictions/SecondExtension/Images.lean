module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.Words
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed
import Mathlib.Tactic.FinCases

/-!
# Marked generators and candidate images

The proposed images are the discovery witnesses recorded in
`LocalRestrictions/source/extension-images.json`. The inverse words were found
by evaluating the same normal forms with the image assignment. All equations
involving these data are proved in the certificate modules; the data alone
assert no homomorphism property.
Source: Parrott (1972), §5, p.683, with the Atlas1600 marking.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.SecondExtension
open ExceptionalParabolics RelativeSecondBlockLayers
open OuterOddSubgroups.OverlapCentralizers

private theorem s_mem (i : ParrottGenerator) (hi : i ≠ .r1) (hi8 : i ≠ .r8) :
    atlas1600ParrottAssignment i ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  apply Subgroup.subset_closure
  cases i <;> simp_all

private theorem generator_mem (a : Fin 9) : SecondOrder.generator a ∈ second := by
  fin_cases a
  · exact reflection_mem_second
  all_goals apply sylow_le_second; apply s_mem <;> decide

def gen (a : Fin 9) : second := ⟨SecondOrder.generator a, by exact generator_mem a⟩

def imageIndex : Fin 9 → Fin 2048 × Fin 3 :=
  ![(1224, 1), (10, 0), (9, 0), (76, 0), (16, 0), (41, 0), (193, 0), (456, 0), (1168, 0)]

def inverseIndex : Fin 9 → Fin 2048 × Fin 3 :=
  ![(1154, 1), (10, 0), (9, 0), (71, 0), (16, 0), (34, 0), (193, 0), (386, 0), (1233, 0)]

def images {G : Type*} [Group G] (g : Fin 9 → G) (a : Fin 9) : G :=
  word g (imageIndex a).1 * rep g (imageIndex a).2

def perm : second →* Equiv.Perm (Fin 1600) where
  toFun x := x.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem perm_injective : Function.Injective perm := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

def packedGen (i : Fin 9) : Equiv.Perm (Fin 1600) :=
  Packed.perm ⟨i.val + 1, by omega⟩

theorem perm_gen (i : Fin 9) : perm (gen i) = packedGen i := by
  change (SecondOrder.generator i).val = packedGen i
  rw [SecondOrder.generator, atlas1600ParrottAssignment_val, packedGen, Packed.perm_eq]
  fin_cases i <;> rfl

theorem word_gen_val (n : Fin 2048) : (word gen n).val = atlas1600SylowTwoNormalForm n := by
  rw [atlas1600SylowTwoNormalForm_eq]
  rfl

theorem rep_gen_val (i : Fin 3) : (rep gen i).val = SecondOrder.rep i := rfl

theorem normalForm_gen (p : Fin 2048 × Fin 3) :
    word gen p.1 * rep gen p.2 = secondNormalForm p := by
  apply Subtype.ext
  exact congrArg₂ (· * ·) (word_gen_val p.1) (rep_gen_val p.2)

theorem gen_generates : Subgroup.closure (Set.range gen) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨⟨n, i⟩, rfl⟩ := secondNormalForm_surjective x
  rw [← normalForm_gen]
  simp only [word, rep]
  repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.pow_mem
    | exact Subgroup.subset_closure ⟨_, rfl⟩

end Tits.AmalgamRigidity.SecondExtension
