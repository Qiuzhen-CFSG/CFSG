module

public import Theory.SpecificGroups.SL2.PrimeIcosahedral
public import Theory.SpecificGroups.AlternatingFiveTriangle
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The exceptional isomorphism PSL₂(5) ≃ PSL₂(4)

The explicit matrix parameters t=3, a=0, b=4 over ZMod 5 satisfy the
icosahedral relations. The proved alternating-five presentation supplies
an injective A₅ homomorphism. Both groups have order sixty, so it is an
isomorphism. Composing with the faithful five-point construction of
PSL₂(4) gives the comparison of the two actual matrix models.

This accounts for the Bender overlap in Aschbacher–Smith 1.1.5(3)(e)
and 2.3.9(7)(a,e), printed pp.502 and 525–526. All constructions and
cardinality formulas are reused from the indicated project modules.
-/

@[expose] public section

open scoped MatrixGroups
namespace Matrix.ProjectiveSpecialLinearGroup

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The prime-field projective group is the actual alternating group A₅. -/
theorem equiv_alternatingGroup_five :
    Nonempty (PSL(2, ZMod 5) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨x, y, hne, hx, hy, hxy⟩ :=
    Matrix.SpecialLinearGroup.Icosahedral.exists_projective_generators
      (3 : ZMod 5) 0 4 (by decide) (by decide)
  obtain ⟨f, hf⟩ := alternatingGroup.exists_injective_hom_of_triangle x y hne hx hy hxy
  have hcard : Nat.card PSL(2, ZMod 5) = 60 := by
    have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 5) 2
    norm_num [Fin.prod_univ_succ] at h
    rw [Nat.card_eq_fintype_card]
    omega
  have hbij := (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, by
    rw [hcard, nat_card_alternatingGroup]
    norm_num [Nat.factorial]⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

/-- The Fermat-prime parameter five is already a characteristic-two Bender model. -/
theorem five_equiv_four :
    Nonempty (PSL(2, ZMod 5) ≃* PSL(2, GaloisField 2 2)) := by
  obtain ⟨e5⟩ := equiv_alternatingGroup_five
  obtain ⟨e4⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  exact ⟨e5.trans e4.symm⟩

end Matrix.ProjectiveSpecialLinearGroup

end
