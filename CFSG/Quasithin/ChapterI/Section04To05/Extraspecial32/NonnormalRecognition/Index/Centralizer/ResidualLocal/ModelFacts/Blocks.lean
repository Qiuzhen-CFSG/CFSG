module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.ModelDefinitions
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Marking.Model
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Two four-point blocks in the marked centralizer

Pairs of permutations with equal sign, whose first member centralizes
`(01)(23)`, embed into the actual centralizer in A₈. The domain and codomain
both have order 96, so this embedding is an isomorphism. Requiring the second
member to centralize the same double transposition gives order 32 and a
Sylow subgroup centralized by the literal mark `z8`.

The finite counts enumerate pairs of four-point permutations only.
Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, with point labels shifted to 0,…,7.
-/

@[expose] public section
open Equiv Equiv.Perm Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.ResidualModel

def fourMark : Perm (Fin 4) := swap 0 1 * swap 2 3

def Blocks : Subgroup (Perm (Fin 4) × Perm (Fin 4)) where
  carrier := {p | Commute p.1 fourMark ∧ sign p.1 * sign p.2 = 1}
  one_mem' := by simp [Commute]
  mul_mem' := by
    intro a b ha hb
    refine ⟨ha.1.mul_left hb.1, ?_⟩
    change sign (a.1 * b.1) * sign (a.2 * b.2) = 1
    rw [map_mul, map_mul, mul_mul_mul_comm, ha.2, hb.2, one_mul]
  inv_mem' := by
    intro a ha
    refine ⟨ha.1.inv_left, ?_⟩
    change sign a.1⁻¹ * sign a.2⁻¹ = 1
    rw [map_inv, map_inv, ← mul_inv, ha.2, inv_one]
instance blocksDecidable : DecidablePred (· ∈ Blocks) := fun p =>
  inferInstanceAs (Decidable (p.1 * fourMark = fourMark * p.1 ∧ sign p.1 * sign p.2 = 1))

theorem blocks_card : Nat.card Blocks = 96 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def blockPerm : Perm (Fin 4) × Perm (Fin 4) →* Perm (Fin 8) :=
  finSumFinEquiv.permCongrHom.toMonoidHom.comp (sumCongrHom (Fin 4) (Fin 4))

theorem blockPerm_injective : Function.Injective blockPerm :=
  finSumFinEquiv.permCongrHom.injective.comp sumCongrHom_injective

theorem blockPerm_sign (p : Perm (Fin 4) × Perm (Fin 4)) :
    sign (blockPerm p) = sign p.1 * sign p.2 := by
  change sign (finSumFinEquiv.permCongr (Perm.sumCongr p.1 p.2)) = _
  rw [sign_permCongr, sign_sumCongr]

theorem blockPerm_t : blockPerm (fourMark, 1) = (t8 : Perm (Fin 8)) := by decide +kernel

def blocksToC : Blocks →* C where
  toFun p := ⟨⟨blockPerm p.val, mem_alternatingGroup.mpr
    ((blockPerm_sign p.val).trans p.property.2)⟩, mem_centralizer_singleton_iff.mpr (by
      apply Subtype.ext
      change blockPerm p.val * (t8 : Perm (Fin 8)) = (t8 : Perm (Fin 8)) * blockPerm p.val
      rw [← blockPerm_t, ← map_mul, ← map_mul]
      exact congrArg blockPerm (Prod.ext p.property.1.eq (by simp)))⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one blockPerm
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; exact map_mul blockPerm a.val b.val

theorem blocksToC_injective : Function.Injective blocksToC := by
  intro a b h
  exact Subtype.ext (blockPerm_injective (congrArg (fun x : C => (x.val : Perm (Fin 8))) h))

noncomputable def blocksEquiv : Blocks ≃* C :=
  MulEquiv.ofBijective blocksToC (blocksToC_injective.bijective_of_nat_card_le
    (by rw [Marking.t8_centralizer_card, blocks_card]))

def centralBlocks : Subgroup Blocks :=
  (centralizer ({fourMark} : Set (Perm (Fin 4)))).comap
    ((MonoidHom.snd _ _).comp Blocks.subtype)
instance centralBlocksDecidable : DecidablePred (· ∈ centralBlocks) := fun p =>
  decidable_of_iff (p.val.2 * fourMark = fourMark * p.val.2)
    mem_centralizer_singleton_iff.symm

theorem centralBlocks_card : Nat.card centralBlocks = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def blocksZ : Blocks := ⟨(fourMark, fourMark), by
  constructor
  · exact Commute.refl _
  · decide +kernel⟩

theorem blocksToC_z : blocksToC blocksZ = z := by
  apply Subtype.ext
  apply Subtype.ext
  decide +kernel

theorem blocksZ_mem : blocksZ ∈ centralBlocks :=
  mem_centralizer_singleton_iff.mpr rfl

theorem blocksZ_commutes (a : Blocks) (ha : a ∈ centralBlocks) : Commute blocksZ a := by
  apply Subtype.ext
  exact Prod.ext a.property.1.symm.eq (mem_centralizer_singleton_iff.mp ha).symm

/-- The simultaneous marked centralizer is a Sylow subgroup of order 32. -/
theorem exists_central_sylow : ∃ T : Sylow 2 C,
    z ∈ (T : Subgroup C) ∧ ∀ a ∈ (T : Subgroup C), Commute z a := by
  let S := centralBlocks.map blocksToC
  have hc : Nat.card S = 32 :=
    (Nat.card_congr (centralBlocks.equivMapOfInjective blocksToC blocksToC_injective).toEquiv).symm.trans
      centralBlocks_card
  have hp : IsPGroup 2 S := IsPGroup.of_card (n := 5) (by norm_num [hc])
  have hi : ¬ 2 ∣ S.index := by
    have hm := S.card_mul_index
    rw [hc, Marking.t8_centralizer_card] at hm
    have he : S.index = 3 := by omega
    simp [he]
  refine ⟨hp.toSylow hi, ?_, ?_⟩
  · exact mem_map.mpr ⟨blocksZ, blocksZ_mem, blocksToC_z⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_map.mp ha
    rw [← blocksToC_z]
    exact (blocksZ_commutes b hb).map blocksToC
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.ResidualModel

end
