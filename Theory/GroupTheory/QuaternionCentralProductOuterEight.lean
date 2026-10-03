module

public import Theory.GroupTheory.QuaternionCentralProductAxisBlocks
public import Theory.GroupTheory.QuaternionCentralProductAxisKernel
public import Theory.GroupTheory.QuaternionCentralProductOuterWreath
public import Theory.GroupTheory.WreathTwoSylowModel

/-!
# Order-eight subgroups of the quaternion Frattini outer image

For an extraspecial group of order thirty-two which is the central product of
two quaternion groups, every order-eight two-subgroup of the automorphism
image on the Frattini quotient is dihedral.

The six cyclic subgroups of order four form two intrinsic triples. Their action
embeds in `SL₂(2) ≀ C₂`, and its kernel equals the Frattini action kernel. Thus
the actual Frattini outer image embeds in this wreath product. An order-eight
two-subgroup maps onto a Sylow subgroup, whose dihedral model is already known.
This uses the structure of the outer image, not merely the subgroup's order.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.390,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Subgroup

/-- The actual Frattini automorphism image of a quaternion central product
embeds faithfully in the two-factor `SL₂(2)` wreath product. -/
public theorem quaternion_central_product_frattini_outer_wreath_embedding
    {H : Type*} [Group H] [Finite H] [IsExtraspecial 2 H]
    (hcard : Nat.card H = 32) (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) :
    ∃ f : (quotientAut (frattini H)).range →*
        RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
          (Multiplicative (ZMod 2)), Function.Injective f := by
  obtain ⟨e, he⟩ := exists_cyclicFourSubgroups_equiv_fin3_mul_zmod2
    B C hB hC hinter hcomm hjoin
  exact exists_frattini_outer_wreath_embedding_of_cyclicFour_coordinates e he
    (quaternion_central_product_axis_kernel hcard B C hB hC hinter hcomm hjoin)

/-- Every order-eight two-subgroup of the quaternion Frattini outer image is
isomorphic to the dihedral group of order eight. -/
public theorem quaternion_central_product_frattini_outer_eight_dihedral
    {H : Type*} [Group H] [Finite H] [IsExtraspecial 2 H]
    (hcard : Nat.card H = 32) (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (U : Subgroup (MulAut (H ⧸ frattini H)))
    (hU : U ≤ (quotientAut (frattini H)).range)
    (hUp : IsPGroup 2 U) (hUcard : Nat.card U = 8) :
    Nonempty (U ≃* DihedralGroup 4) := by
  obtain ⟨f, hf⟩ := quaternion_central_product_frattini_outer_wreath_embedding
    hcard B C hB hC hjoin hinter hcomm
  let g := f.comp (inclusion hU)
  have hg : Function.Injective g := hf.comp (inclusion_injective hU)
  let e := MonoidHom.ofInjective hg
  obtain ⟨P, hP⟩ := (hUp.of_equiv e).exists_le_sylow
  obtain ⟨eP⟩ := wreath_two_sylow_mulEquiv_dihedral_four P
  have hcardP : Nat.card P = 8 := by
    rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
  have hcardR : Nat.card g.range = 8 := (Nat.card_congr e.toEquiv).symm.trans hUcard
  have heq : g.range = (P : Subgroup _) := eq_of_le_of_card_ge hP (by
    rw [hcardR, hcardP])
  exact ⟨e.trans ((MulEquiv.subgroupCongr heq).trans eP)⟩

end Subgroup
