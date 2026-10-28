module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.Geometry
public import Theory.Mathieu.M22.CentralCoverConjugation

/-!
# From a native representative calculation to arbitrary source J

Recognize H as a genuine conjugate of the fixed pair stabilizer, lift that
conjugator through the specified central quotient, and transport both
subgroups in the intersection by the same inner automorphism. Residual
monotonicity then places the center in the residual of the full preimage.
Two-core recognition transports through the same actual group equivalence.

These are conditional assembly lemmas for I.2.2(6a), printed pp.410 and
412. The fixed-pair residual calculation and quartic model isomorphism
remain explicit inputs, to be supplied by the compatible model calculations.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
/-- Every source pullback is isomorphic through a lifted native conjugator
to the pullback of the fixed disjoint-pair stabilizer. -/
theorem sourceJ_preimage_equiv (e : (K ⧸ center K) ≃* M22)
    (H : Subgroup M22) (hH : IsSourceJ H) :
    Nonempty (preimage e m22DisjointPairStabilizer ≃* preimage e H) := by
  obtain ⟨g, hH, _, _, _⟩ := sourceJ_disjoint_flag H hH
  obtain ⟨k, rfl⟩ := projection_surjective e g
  exact ⟨(preimageConjEquiv e m22DisjointPairStabilizer k).trans
    (MulEquiv.subgroupCongr (congrArg (preimage e) hH.symm))⟩

/-- A proved fixed-pair calculation supplies an actual hexad for arbitrary H
and then the desired placement in O²(J). This does not assert that input. -/
theorem sourceJ_residual_of_fixed_pair (e : (K ⧸ center K) ≃* M22)
    (H : Subgroup M22) (hH : IsSourceJ H)
    (hbase : ∃ B ∈ m22Blocks,
      center K ≤ (pResidual 2
        (hexadPreimage e B ⊓ preimage e m22DisjointPairStabilizer : Subgroup K)).map
          (hexadPreimage e B ⊓ preimage e m22DisjointPairStabilizer).subtype) :
    (∃ B ∈ m22Blocks,
      center K ≤ (pResidual 2 (hexadPreimage e B ⊓ preimage e H : Subgroup K)).map
        (hexadPreimage e B ⊓ preimage e H).subtype) ∧
      center K ≤ (pResidual 2 (preimage e H)).map (preimage e H).subtype := by
  obtain ⟨g, hHmap, _, _, _⟩ := sourceJ_disjoint_flag H hH
  obtain ⟨k, rfl⟩ := projection_surjective e g
  obtain ⟨B, hB, hz⟩ := hbase
  have hJ : preimage e H =
      (preimage e m22DisjointPairStabilizer).map (MulAut.conj k).toMonoidHom := by
    rw [hHmap, preimage_map_conj]
  have hI : hexadPreimage e (projection e k • B) =
      (hexadPreimage e B).map (MulAut.conj k).toMonoidHom := by
    rw [hexadPreimage, MulAction.stabilizer_smul_eq_stabilizer_map_conj, preimage_map_conj]
    rfl
  have hX : hexadPreimage e (projection e k • B) ⊓ preimage e H =
      (hexadPreimage e B ⊓ preimage e m22DisjointPairStabilizer).map
        (MulAut.conj k).toMonoidHom := by
    rw [hI, hJ, map_inf _ _ _ (MulAut.conj k).injective]
  have hz' := center_le_residual_conjugate _ k hz
  rw [← hX] at hz'
  exact ⟨⟨projection e k • B, m22_smul_block_mem _ _ hB, hz'⟩,
    hz'.trans (embedded_pResidual_mono 2 inf_le_right)⟩

omit [Finite K] in
/-- Recognition of the fixed pair's actual two-core transports to arbitrary H.
The model is a genuine group with a multiplicative equivalence, not a tag. -/
theorem sourceJ_twoCore_model_of_fixed_pair (e : (K ⧸ center K) ≃* M22)
    (H : Subgroup M22) (hH : IsSourceJ H) (M : Type*) [Group M]
    (hbase : Nonempty (pCore 2 (preimage e m22DisjointPairStabilizer) ≃* M)) :
    Nonempty (pCore 2 (preimage e H) ≃* M) := by
  obtain ⟨a⟩ := sourceJ_preimage_equiv e H hH
  obtain ⟨b⟩ := hbase
  let c := ((pCore 2 (preimage e m22DisjointPairStabilizer)).equivMapOfInjective
    a.toMonoidHom a.injective).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 a))
  exact ⟨c.symm.trans b⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
