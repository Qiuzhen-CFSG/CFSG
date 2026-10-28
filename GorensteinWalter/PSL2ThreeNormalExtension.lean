module
public import GorensteinWalter.PGammaL2NormalExtension

/-!
# Linear realization of a self-centralizing prescribed PSL2 core

A normal PSL2 subgroup with trivial centralizer gives a faithful conjugation
action. A compatible actual equivalence PGL2 ≃ Aut(PSL2) realizes that action
in the linear subgroup of PGammaL2, preserving the specified core map. Its
field-automorphism image is trivial and in particular has odd order.

This is the shared field-three normal-extension argument: the actual
PGL2(3) ≃ Aut(A4) theorem supplies the equivalence to both dihedral and
semidihedral Sylow consumers. The proof is extracted unchanged from
NormalPSL2Semilinear, and uses no ambient Sylow assumption. It supports
Alperin--Brauer--Gorenstein II.3, Propositions 3 and 4.
-/

namespace GorensteinWalter
universe u

public theorem exists_normal_psl2_linear_embedding_of_aut_equiv
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (e : N ≃* PSL2 K)
    (hC : Subgroup.centralizer (N : Set G) = ⊥)
    (eAut : PGL2 K ≃* MulAut (PSL2 K))
    (heAut : ∀ x : PSL2 K, eAut (Matrix.ProjectiveSpecialLinearGroup.toPGL x) =
      MulAut.conj x) :
    ∃ f : G →* PGammaL2 K, Function.Injective f ∧
      (∀ n : N, f n = SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (e n))) ∧
      Odd (Nat.card (pGammaL2FieldProjection K f.range).range) := by
  let a := normalPSL2ConjAction N K e
  have ha : Function.Injective a := (MulAut.congr e).injective.comp
    (conjNormal_injective_of_centralizer_eq_bot N hC)
  let f : G →* PGammaL2 K := SemidirectProduct.inl.comp
    (eAut.symm.toMonoidHom.comp a)
  refine ⟨f, SemidirectProduct.inl_injective.comp (eAut.symm.injective.comp ha), ?_, ?_⟩
  · intro n
    change SemidirectProduct.inl (eAut.symm (a n)) = _
    congr 1
    apply eAut.injective
    rw [eAut.apply_symm_apply, heAut]
    change MulAut.congr e (MulAut.conjNormal (H := N) n.val) = _
    rw [MulAut.conjNormal_val]
    ext x
    simp [MulAut.congr, MulAut.conj_apply]
  · have hrange : (pGammaL2FieldProjection K f.range).range = ⊥ := by
      apply le_bot_iff.mp
      rintro σ ⟨x, rfl⟩
      obtain ⟨g, hg⟩ := x.property
      change x.val.right = 1
      rw [← hg]
      rfl
    rw [hrange]
    simp

end GorensteinWalter
