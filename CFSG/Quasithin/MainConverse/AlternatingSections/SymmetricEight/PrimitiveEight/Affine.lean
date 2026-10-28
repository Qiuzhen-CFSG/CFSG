module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.LinearModels
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Theory.AtlasPort.OtherSporadic.GroupTheory.TransitiveNoncommutative
public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.PGroup.Omega

/-!
# The affine branch in primitive degree eight

A nontrivial abelian normal subgroup of a faithful primitive group is transitive
and regular, hence has order eight. Its characteristic first omega subgroup is
again normal and transitive, so it is the whole subgroup. Thus the normal group
is elementary abelian of order eight.

Conjugation has exactly this normal subgroup as its kernel. The actual
vector-space automorphism equivalence identifies its automorphism group with
GL₃(2) = SL₃(2). The known simple sections of this matrix group, together with
the solvable normal kernel, therefore give all simple sections of the original
group. This includes every primitive affine subgroup, without assuming an
affine subgroup list or confusing the translation group with the cyclic C₈.

This supplies the affine branch of the degree-eight calculation for condition K
in Aschbacher–Smith, Theorem 0.1.2(3), printed pp.4 and 482. The normal-orbit and
regular-action facts are reused from the attributed ATLAS ports imported above.
-/

open scoped IsMulCommutative
open MulAction

namespace CFSG.Quasithin.MainConverse
open CFSG.KnownSimple

private theorem abelian_normal_eight {G : Type*} [Group G] [Finite G]
    [MulAction G (Fin 8)] [FaithfulSMul G (Fin 8)] [IsPreprimitive G (Fin 8)]
    (N : Subgroup G) [N.Normal] [IsMulCommutative N] (hN : N ≠ ⊥) :
    Nat.card N = 8 ∧ IsElementaryAbelian 2 N := by
  let : IsPretransitive N (Fin 8) := Atlas.GroupTheory.normal_pretransitive N hN
  have hc : Nat.card N = 8 := by
    simpa using Atlas.GroupTheory.card_eq_degree_of_commutative (G := N)
      (0 : Fin 8) (fun _ _ => mul_comm _ _)
  let O := omega₁ N (p := 2)
  let : O.Characteristic := omega₁_characteristic N
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative N
  let E := O.map N.subtype
  let : E.Normal := inferInstance
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map_subtype
  have hE : E ≠ ⊥ := omega₁_map_subtype_ne_bot N 2 (by simp [hc])
  let : IsPretransitive E (Fin 8) := Atlas.GroupTheory.normal_pretransitive E hE
  have hcE : Nat.card E = 8 := by
    simpa using Atlas.GroupTheory.card_eq_degree_of_commutative (G := E)
      (0 : Fin 8) (fun _ _ => mul_comm _ _)
  have heq : E = N := Subgroup.eq_of_le_of_card_ge
    (Subgroup.map_subtype_le O) (by omega)
  exact ⟨hc, heq ▸ inferInstance⟩

private theorem conjNormal_ker_of_abelian_transitive {G X : Type*} [Group G]
    [MulAction G X] [FaithfulSMul G X] (a : X)
    (N : Subgroup G) [N.Normal] [IsMulCommutative N] [IsPretransitive N X] :
    (MulAut.conjNormal : G →* MulAut N).ker = N := by
  ext g
  constructor
  · intro hg
    have hcomm (n : N) : g * (n : G) = (n : G) * g := by
      have h := congrArg (fun e : MulAut N => (e n : G)) hg
      change g * (n : G) * g⁻¹ = (n : G) at h
      exact mul_inv_eq_iff_eq_mul.mp h
    obtain ⟨n, hn⟩ := exists_smul_eq N a (g • a)
    have heq : g = (n : G) := by
      apply eq_of_smul_eq_smul (α := X)
      intro x
      obtain ⟨k, rfl⟩ := exists_smul_eq N a x
      change g • ((k : G) • a) = (n : G) • ((k : G) • a)
      rw [← mul_smul, hcomm k, mul_smul, ← hn]
      change k • (n • a) = n • (k • a)
      rw [← mul_smul, mul_comm k n, mul_smul]
    exact heq ▸ n.property
  · intro hg
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    change g * (n : G) * g⁻¹ = (n : G)
    have hcomm : g * (n : G) = (n : G) * g :=
      congrArg Subtype.val (mul_comm (⟨g, hg⟩ : N) n)
    rw [hcomm, mul_inv_cancel_right]

/-- All sections in the primitive affine branch are constructed. -/
public theorem primitiveEight_isKGroup_of_abelian_normal
    (U : Subgroup (Equiv.Perm (Fin 8))) [IsPreprimitive U (Fin 8)]
    (N : Subgroup U) [N.Normal] [IsMulCommutative N] (hN : N ≠ ⊥) :
    IsKGroup IsConstructedCarrier U := by
  obtain ⟨hcard, hE⟩ := abelian_normal_eight N hN
  let := hE
  let : IsPretransitive N (Fin 8) := Atlas.GroupTheory.normal_pretransitive N hN
  obtain ⟨e⟩ := elementaryEight_mulAut_equiv_GL N hcard
  let eSL := e.trans Matrix.PSL3Two.equivGL.symm
  have hAut : IsKGroup IsConstructedCarrier (MulAut N) :=
    SymmetricEight.isKGroup_constructed_of_injective sl3Two_isKGroup_constructed
      eSL.toMonoidHom eSL.injective
  let φ : U →* MulAut N := MulAut.conjNormal
  have hker : φ.ker = N := conjNormal_ker_of_abelian_transitive (0 : Fin 8) N
  have hq : IsKGroup IsConstructedCarrier (U ⧸ N) := by
    let eqv := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)
    exact (hAut.of_injective φ.range.subtype Subtype.val_injective).of_injective
      eqv.toMonoidHom eqv.injective
  exact IsKGroup.of_normal_quotient N (solvable_isKGroup_constructed _) hq

end CFSG.Quasithin.MainConverse
