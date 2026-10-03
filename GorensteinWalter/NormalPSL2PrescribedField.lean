module
public import GorensteinWalter.NormalPSL2CoreUniquenessGeneral
public import GorensteinWalter.NormalPSL2ToPGammaL2Apply
public import GorensteinWalter.PGammaL2PureSemilinear

/-!
# Semilinear embeddings over a prescribed PSL2 field

Let a finite odd-core-free group have dihedral Sylow two-subgroups and a
specified normal subgroup isomorphic to PSL2(K), where K is an odd finite
field of order greater than three. The ambient group embeds into PGammaL2(K)
with the specified core mapped by its canonical inner inclusion, and its
field-automorphism image has odd order. The field of order nine is included.

The normal-core centralizer theorem makes conjugation faithful. The proved
semilinear automorphism theorem, supplied with the actual prime-power
cardinality, realizes this conjugation over the specified field. Transporting
the Sylow condition to the image then gives oddness of its field projection.
No automorphism-surjectivity or self-centralizing assumption remains.

This is the large-field quotient step of Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 3 (article pages 24-25). The field of order
three is handled separately by its actual PGL2 conjugation model.
-/

namespace GorensteinWalter

universe u

public theorem exists_prescribed_field_semilinear_embedding
    {G : Type u} [Group G] [Finite G]
    (hGd : HasDihedralSylowTwo G) (hO : pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PSL2 K) :
    ∃ f : G →* PGammaL2 K, Function.Injective f ∧
      (∀ n : N, f n = SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (e n))) ∧
      Odd (Nat.card (pGammaL2FieldProjection K f.range).range) := by
  have hC := normal_psl2_centralizer_eq_bot hGd hO N inferInstance K hK e
  obtain ⟨p, d, hp, hpodd, hd, hKd⟩ := hK
  have hK : IsOddPrimePower (Nat.card K) := ⟨p, d, hp, hpodd, hd, hKd⟩
  let : Fact p.Prime := ⟨hp⟩
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKd hK hcard
  let f := normalPSL2ToPGammaL2 N K hK hcard e hsurj
  have hf : Function.Injective f :=
    normalPSL2ToPGammaL2_injective N K hK hcard e hC hsurj
  let eG : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun a b hab => hf (congrArg Subtype.val hab), f.rangeRestrict_surjective⟩
  let : Finite f.range := Finite.of_surjective eG eG.surjective
  refine ⟨f, hf, ?_, ?_⟩
  · exact normalPSL2ToPGammaL2_apply_subtype N K hK hcard e hsurj
  · exact pGammaL2_field_projection_range_odd_of_dihedral K hK hcard f.range
      (normalPSL2ToPGammaL2_range_contains_psl N K hK hcard e hsurj)
      (hasDihedralSylowTwo_of_mulEquiv eG.symm hGd)

end GorensteinWalter
