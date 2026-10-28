module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.Reduction

/-!
# Common geometric coordinates for the two rank-one design parabolics

The two candidates are literal conjugates, by the same design automorphism,
of the three-pair stabilizer and the pair--hexad stabilizer. Both preserve the
same conjugated hexad. Their proposed exhaustive classification is isolated
as DesignCatalogueAt, a separate geometric obligation. No source catalogue
is inferred from this input contract.

Source: Aschbacher--Smith, 14.4.12, printed pp.1011--1012. The classification
will use the native M₂₂ solvable-Sylow-overgroup theorem and the six-point
hexad restriction; ordering the native lifts requires the actual binary action.
-/

@[expose] public section
open Subgroup
open Sporadic.Mathieu
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue
noncomputable def partitionAt (g : m22DesignAut) : Subgroup m22DesignAut :=
  M22ValueBound.Concrete.outerSecond.map (MulAut.conj g).toMonoidHom
noncomputable def pairAt (g : m22DesignAut) : Subgroup m22DesignAut :=
  outerPairHexad.map (MulAut.conj g).toMonoidHom

/-- The remaining design calculation, stated independently of the binary
representation and the cubic cover. Its equality concerns every index-three
overgroup of the fixed Sylow subgroup. The quotient witnesses are used to
construct and uniquely determine the native lifts. This is an input contract,
not an assertion that the geometric classification is already proved. -/
structure DesignCatalogueAt (U : Sylow 2 m22DesignAut) (g : m22DesignAut) : Prop where
  overgroups : rankOneOvergroups U = {partitionAt g, pairAt g}
  partition_quotient : Nonempty (((partitionAt g ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut) ⧸
    pCore 2 (partitionAt g ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut)) ≃* Equiv.Perm (Fin 3))
  pair_quotient : Nonempty (((pairAt g ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut) ⧸
    pCore 2 (pairAt g ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut)) ≃* Equiv.Perm (Fin 3))

lemma partitionAt_le_hexad (g : m22DesignAut) :
    partitionAt g ≤ MulAction.stabilizer m22DesignAut (g • m22Hexad123) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  apply map_mono
  intro x hx
  change x • m22Hexad123 = m22Hexad123
  rw [← M22ValueBound.Concrete.hexadPartition_union]
  have h : x • M22ValueBound.Concrete.hexadPartition.biUnion id =
      (x • M22ValueBound.Concrete.hexadPartition).biUnion id := by
    simp only [Finset.smul_finset_def, Finset.image_biUnion, Finset.biUnion_image]
    rfl
  rw [h, MulAction.mem_stabilizer_iff.mp hx]

lemma pairAt_le_hexad (g : m22DesignAut) :
    pairAt g ≤ MulAction.stabilizer m22DesignAut (g • m22Hexad123) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact map_mono (show outerPairHexad ≤ MulAction.stabilizer m22DesignAut m22Hexad123 from inf_le_left)


end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue
