module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Intrinsic
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers.WordModels

/-!
# Coordinates for the exceptional A₇ plane actors

The four-plus-three partition stabilizer has four candidate two-perfect
subgroups with cubic two-core quotient: the tail three-cycle, the natural A₄,
and the two diagonal A₄ embeddings. The plane action distinguishes the two
diagonals. These definitions retain both embeddings; neither is selected by
its name. The catalogue and the representation-dependent selection are
separate assertions, not consequences of these definitions.

The generators agree literally with the seven-point models in
`AlternatingSeven.ThreeResidualLocals`. The natural and cyclic candidates
already supply the single-three-cycle alternative of `ActorWitness`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932.
-/

@[expose] public section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue

/-- Relabelling all seven letters, including by an odd permutation, induces
an actual automorphism of the alternating group. -/
def relabelling (g : Perm (Fin 7)) : MulAut A7 where
  toFun a := ⟨g * a.val * g⁻¹, by
    rw [Perm.mem_alternatingGroup]
    simp only [map_mul, map_inv, show Perm.sign a.val = 1 from a.property,
      mul_one, mul_inv_cancel]⟩
  invFun a := ⟨g⁻¹ * a.val * g, by
    rw [Perm.mem_alternatingGroup]
    simp only [map_mul, map_inv, show Perm.sign a.val = 1 from a.property,
      mul_one, inv_mul_cancel]⟩
  left_inv a := Subtype.ext (by change g⁻¹ * (g * a.val * g⁻¹) * g = a.val; group)
  right_inv a := Subtype.ext (by change g * (g⁻¹ * a.val * g) * g⁻¹ = a.val; group)
  map_mul' a b := Subtype.ext (by
    change g * (a.val * b.val) * g⁻¹ = (g * a.val * g⁻¹) * (g * b.val * g⁻¹)
    group)

theorem relabelling_isThreeCycle (g : Perm (Fin 7)) (a : A7)
    (ha : a.val.IsThreeCycle) : (relabelling g a).val.IsThreeCycle := by
  change (g * a.val * g⁻¹).cycleType = {3}
  rw [Perm.cycleType_conj]
  exact ha

/-- The cubic generator on the first three letters. -/
def naturalThree : A7 :=
  ⟨AlternatingSeven.ThreeResidualLocals.naturalThree,
    AlternatingSeven.ThreeResidualLocals.model_generators_even.2.1⟩

/-- The double transposition in the four-letter block. -/
def fourFlip : A7 :=
  ⟨AlternatingSeven.ThreeResidualLocals.fourFlip,
    AlternatingSeven.ThreeResidualLocals.model_generators_even.1⟩

/-- The disjoint cubic generator on the three-letter block. -/
def tailThree : A7 :=
  ⟨swap 4 5 * swap 5 6, by rw [Perm.mem_alternatingGroup]; decide⟩

/-- The literal even stabilizer of `{0,1,2,3}`. -/
def blockStabilizer : Subgroup A7 :=
  AlternatingSeven.ThreeResidualLocals.fourPointSetwiseStabilizer.comap
    (alternatingGroup (Fin 7)).subtype

def cyclicActor : Subgroup A7 := zpowers tailThree
def naturalActor : Subgroup A7 := closure ({naturalThree, fourFlip} : Set A7)
def diagonalPlus : Subgroup A7 := closure ({naturalThree * tailThree, fourFlip} : Set A7)
def diagonalMinus : Subgroup A7 := closure ({naturalThree * tailThree ^ 2, fourFlip} : Set A7)

theorem naturalThree_isThreeCycle : naturalThree.val.IsThreeCycle := by
  rw [Perm.IsThreeCycle]
  decide

theorem tailThree_isThreeCycle : tailThree.val.IsThreeCycle := by
  rw [Perm.IsThreeCycle]
  decide

theorem generators_mem_block : naturalThree ∈ blockStabilizer ∧
    fourFlip ∈ blockStabilizer ∧ tailThree ∈ blockStabilizer := by
  change (∀ x : Fin 7, x.val < 4 ↔ (naturalThree.val x).val < 4) ∧
    (∀ x : Fin 7, x.val < 4 ↔ (fourFlip.val x).val < 4) ∧
    (∀ x : Fin 7, x.val < 4 ↔ (tailThree.val x).val < 4)
  decide +kernel

theorem cyclicActor_le_block : cyclicActor ≤ blockStabilizer :=
  zpowers_le.mpr generators_mem_block.2.2

theorem naturalActor_le_block : naturalActor ≤ blockStabilizer :=
  (closure_le _).mpr (by
    simpa only [Set.pair_subset_iff, SetLike.mem_coe] using
      And.intro generators_mem_block.1 generators_mem_block.2.1)

theorem diagonalPlus_le_block : diagonalPlus ≤ blockStabilizer :=
  (closure_le _).mpr (by
    simpa only [Set.pair_subset_iff, SetLike.mem_coe] using
      And.intro (blockStabilizer.mul_mem generators_mem_block.1 generators_mem_block.2.2)
        generators_mem_block.2.1)

theorem diagonalMinus_le_block : diagonalMinus ≤ blockStabilizer :=
  (closure_le _).mpr (by
    simpa only [Set.pair_subset_iff, SetLike.mem_coe] using
      And.intro (blockStabilizer.mul_mem generators_mem_block.1
        (blockStabilizer.pow_mem generators_mem_block.2.2 2)) generators_mem_block.2.1)

/-- The natural candidate uses the existing literal permutation subgroup. -/
theorem naturalActor_map : naturalActor.map (alternatingGroup (Fin 7)).subtype =
    AlternatingSeven.ThreeResidualLocals.naturalFour := by
  rw [naturalActor, MonoidHom.map_closure, Set.image_pair]
  rfl

/-- The first diagonal uses the existing literal permutation subgroup. -/
theorem diagonalPlus_map : diagonalPlus.map (alternatingGroup (Fin 7)).subtype =
    AlternatingSeven.ThreeResidualLocals.diagonalFour := by
  rw [diagonalPlus, MonoidHom.map_closure, Set.image_pair]
  rfl

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) A7 W) (P : Submodule (ZMod 2) W)

theorem cyclicActor_witness : ActorWitness ρ P cyclicActor :=
  Or.inl ⟨tailThree, mem_zpowers tailThree, tailThree_isThreeCycle⟩

theorem naturalActor_witness : ActorWitness ρ P naturalActor :=
  Or.inl ⟨naturalThree, subset_closure (by simp), naturalThree_isThreeCycle⟩

theorem cyclicActor_map_witness (g : Perm (Fin 7)) :
    ActorWitness ρ P (cyclicActor.map (relabelling g).toMonoidHom) :=
  Or.inl ⟨relabelling g tailThree,
    ⟨tailThree, mem_zpowers tailThree, rfl⟩,
    relabelling_isThreeCycle g tailThree tailThree_isThreeCycle⟩

theorem naturalActor_map_witness (g : Perm (Fin 7)) :
    ActorWitness ρ P (naturalActor.map (relabelling g).toMonoidHom) :=
  Or.inl ⟨relabelling g naturalThree,
    ⟨naturalThree, subset_closure (by simp), rfl⟩,
    relabelling_isThreeCycle g naturalThree naturalThree_isThreeCycle⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue
