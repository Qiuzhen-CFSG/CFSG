module
public import GorensteinWalter.NormalPSL2PrescribedField
public import GorensteinWalter.PGL2ThreeAutomorphism
public import GorensteinWalter.PSL2ThreeNormalExtension

/-!
# Prescribed-field semilinear embeddings for all odd PSL2 cores

A finite odd-core-free group with dihedral Sylow two-subgroups and a specified
normal PSL2(K) subgroup embeds in PGammaL2(K), with its core mapped by the
canonical inner inclusion. The image of its coefficient projection has odd
order. No odd field order is excluded.

For order greater than three, the prescribed-field embedding theorem combines
the actual semilinear automorphism theorem with the dihedral field-image
constraint. In order three, the proved PGL2-to-AutPSL2 conjugation equivalence
realizes the faithful normal-core action inside the linear layer; its field
projection is trivial. The shared realization proof is imported from
PSL2ThreeNormalExtension. Both cases preserve the supplied core identification.

This assembles the projective quotient step in Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 3 (article pages 24-25), before the central
lift and the exact SL_m/SU_m matrix-model comparison.
-/

namespace GorensteinWalter

universe u

public theorem exists_normal_psl2_semilinear_embedding
    {G : Type u} [Group G] [Finite G]
    (hGd : HasDihedralSylowTwo G) (hO : pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : N ≃* PSL2 K) :
    ∃ f : G →* PGammaL2 K, Function.Injective f ∧
      (∀ n : N, f n = SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (e n))) ∧
      Odd (Nat.card (pGammaL2FieldProjection K f.range).range) := by
  by_cases hcard : Nat.card K = 3
  · obtain ⟨eAut, heAut⟩ := exists_pgl2_equiv_aut_psl2_of_card_three K hcard
    exact exists_normal_psl2_linear_embedding_of_aut_equiv N K e
      (normal_psl2_centralizer_eq_bot hGd hO N inferInstance K hK e) eAut heAut
  · exact exists_prescribed_field_semilinear_embedding hGd hO N K hK
      (lt_of_le_of_ne (odd_prime_power_three_le _ hK) (Ne.symm hcard)) e

end GorensteinWalter
