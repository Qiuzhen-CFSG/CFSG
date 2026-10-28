module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Representation
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.CoreLift
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Geometry.Eigenspaces
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Geometry.Embedding
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Geometry.CentralizerReduction

/-!
# Rank and centralizer bounds for symplectic lift cores

Every elementary abelian two-group embedded in Sp₄ over a field of odd
characteristic has order at most four. Restricting the actual matrix action
to a subgroup of any lifted two-core proves the required bound without
extraspeciality, maximality, or irreducibility assumptions.

For an irreducible full preimage with extraspecial two-core, its relative
centralizer embeds in GL₂(3). The vanishing three-core and the solvable
Fitting argument then put that centralizer inside the two-core.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`. Extraspeciality remains an
explicit input to the centralizer theorem; the rank theorem is unconditional.
-/

namespace Matrix.PSp4Three
open scoped IsMulCommutative

/-- Every elementary abelian two-subgroup of Sp₄ in odd characteristic has order at most four. -/
public theorem elementaryAbelian_card_le_four_sp_four {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) {E : Type*} [Group E] [IsElementaryAbelian 2 E]
    (f : E →* Sp 2 F) (hf : Function.Injective f) : Nat.card E ≤ 4 := by
  let rho : Representation F E (Vector 2 F) :=
    (Representation.ofDistribMulAction F (Sp 2 F) (Vector 2 F)).comp f
  apply NontrivialTwoCore.Geometry.LinearInvolution.card_le_four_of_commuting_involutions
    form form_alternating form_nondegenerate rho
  · intro x y h
    apply hf
    apply ext_action
    intro v
    exact LinearMap.congr_fun h v
  · intro g v
    have hg : g ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) g
    change f g • (f g • v) = v
    rw [← mul_smul, ← map_mul, ← pow_two, hg, map_one, one_smul]
  · intro g x y
    exact preserves (f g) x y
  · intro g h v
    change f g • (f h • v) = f h • (f g • v)
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul, mul_comm g h]
  · exact h2
  · simp [Vector, Index]

/-- The elementary-rank bound for the lifted two-core requires no assumptions on the projective subgroup. -/
public theorem fullPreimage_twoCore_elementary_card_lt_eight
    (M : Subgroup (PSp 2 (ZMod 3)))
    (E : Subgroup (pCore 2 (fullPreimage M))) (hE : IsElementaryAbelian 2 E) :
    Nat.card E < 8 := by
  let := hE
  let f := (fullPreimage M).subtype.comp
    ((pCore 2 (fullPreimage M)).subtype.comp E.subtype)
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  have h := elementaryAbelian_card_le_four_sp_four (by decide : (2 : ZMod 3) ≠ 0) f hf
  omega

/-- The extraspecial two-core of an irreducible full symplectic preimage
contains its relative centralizer. -/
public theorem fullPreimage_twoCore_centralizer_le_of_extraspecial
    (M : Subgroup (PSp 2 (ZMod 3))) (hred : ¬ HasInvariantSubspace M)
    (hspecial : IsExtraspecial 2 (pCore 2 (fullPreimage M))) :
    Subgroup.centralizer (pCore 2 (fullPreimage M) : Set (fullPreimage M)) ≤
      pCore 2 (fullPreimage M) := by
  obtain ⟨f, hf⟩ := NontrivialTwoCore.Geometry.fullPreimage_twoCore_centralizer_gl_two_embedding
    M hred hspecial
  exact NontrivialTwoCore.Geometry.centralizer_le_twoCore_of_gl2_embedding
    (NontrivialTwoCore.Geometry.fullPreimage_threeCore_eq_bot M hred) f hf

end Matrix.PSp4Three
