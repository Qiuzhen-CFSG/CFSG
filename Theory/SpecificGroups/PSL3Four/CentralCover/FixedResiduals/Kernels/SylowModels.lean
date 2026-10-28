module

public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Dihedral Sylow models used by the four-cover restriction theorem

Two explicit upper unitriangular binary matrices generate a dihedral eight
in SL₃(2); its image in PSL₃(2) has the full two-part of order 168.
Double transpositions generate a dihedral four in A₅, which the proved
projective-line isomorphism transports to PSL₂(4). Sylow conjugacy gives
models on every specified Sylow subtype. Multiplication and injectivity of
the two small embeddings are checked by kernel reduction.

These supply the actual image models needed by the central-cover argument
in Aschbacher--Smith 15.3.38, printed p.1137. No cover or multiplier fact is
used in these matrix and permutation calculations.
-/

namespace Matrix.PSL3Four.FixedResidualKernels

private theorem sylow_model_of_embedding {D G : Type*} [Group D] [Finite D]
    [Group G] [Finite G] (f : D →* G) (hf : Function.Injective f)
    (hcard : Nat.card D = 2 ^ (Nat.card G).factorization 2)
    (S : Sylow 2 G) : Nonempty (S ≃* D) := by
  let e := MonoidHom.ofInjective hf
  let T : Sylow 2 G := Sylow.ofCard f.range (by
    rw [← Nat.card_congr e.toEquiv]
    exact hcard)
  exact ⟨(S.equiv T).trans e.symm⟩

private def binaryRotation : PSL3Two.SL := ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by decide⟩
private def binaryReflection : PSL3Two.SL := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩
private def binaryMap : DihedralGroup 4 → PSL3Two.SL
  | .r i => binaryRotation ^ i.val
  | .sr i => binaryReflection * binaryRotation ^ i.val
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private def binaryHom : DihedralGroup 4 →* PSL3Two.SL where
  toFun := binaryMap
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem binaryHom_injective : Function.Injective binaryHom := by decide +kernel

/-- Every Sylow two-subgroup of the actual PSL₃(2) carrier is dihedral of order eight. -/
public theorem psl3Two_sylow_dihedral (S : Sylow 2 PSL3Two.PSL) :
    Nonempty (S ≃* DihedralGroup 4) := by
  apply sylow_model_of_embedding (PSL3Two.equiv.toMonoidHom.comp binaryHom)
    (PSL3Two.equiv.injective.comp binaryHom_injective) _ S
  rw [DihedralGroup.nat_card, PSL3Two.card_PSL]
  decide +kernel

private abbrev A5 := alternatingGroup (Fin 5)
private def fiveRotation : A5 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def fiveReflection : A5 :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def fiveMap : DihedralGroup 2 → A5
  | .r i => fiveRotation ^ i.val
  | .sr i => fiveReflection * fiveRotation ^ i.val
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private def fiveHom : DihedralGroup 2 →* A5 where
  toFun := fiveMap
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem fiveHom_injective : Function.Injective fiveHom := by decide +kernel

/-- Every Sylow two-subgroup of the actual PSL₂(4) carrier is a four-group. -/
public theorem psl2Four_sylow_dihedral (S : Sylow 2 (ProjectiveSpecialLinearGroup (Fin 2) F)) :
    Nonempty (S ≃* DihedralGroup 2) := by
  obtain ⟨e⟩ := ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four card_F
  apply sylow_model_of_embedding (e.symm.toMonoidHom.comp fiveHom)
    (e.symm.injective.comp fiveHom_injective) _ S
  rw [DihedralGroup.nat_card, Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  decide +kernel

end Matrix.PSL3Four.FixedResidualKernels
