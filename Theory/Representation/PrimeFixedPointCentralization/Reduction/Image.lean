module

public import Theory.Representation.PrimeFixedPointCentralization.Reduction.Actions
public import Theory.Representation.Quotient
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The faithful irreducible image of a surviving prime action

An irreducible constituent need not be faithful. Quotienting its full kernel
makes it faithful; a surviving moved element makes the prime-order actor
faithful on the image of the q-group. The q-group image and the actor image
intersect trivially, so their product is the original semidirect product with
the q-group replaced by its image. Minimality descends by equivariant preimages.

This supplies the image step implicit in Aschbacher, *Finite Group Theory*,
second edition, proof of 36.2, printed p.194.
-/

universe u
namespace Representation.PrimeFixedPointCentralization

/-- The minimal faithful irreducible input applies to any irreducible module
on which a moved element of the kernel group still survives. -/
public theorem fixed_vector_of_irreducible_moving
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime] (hqr : q ≠ r)
    (hfixed : MinimalFixedVectorStatement.{u} q r)
    {P A W : Type u} [Group P] [Finite P] [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hP : IsPGroup q P) (hA : Nat.card A = r)
    (φ : A →* MulAut P) (hmin : IsMinimalAction φ)
    (σ : Representation (ZMod 2) (SemidirectProduct P A φ) W)
    (hirr : σ.IsIrreducible)
    (hmoving : ∃ a z, σ (SemidirectProduct.inl (φ a z)) ≠
      σ (SemidirectProduct.inl z)) :
    ∃ v : W, v ≠ 0 ∧ ∀ a : A, σ (SemidirectProduct.inr a) v = v := by
  classical
  let S := SemidirectProduct P A φ
  let : Finite S := Finite.of_equiv (P × A) SemidirectProduct.equivProd.symm
  let G := S ⧸ σ.ker
  let f : S →* G := QuotientGroup.mk' σ.ker
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  let Q : Subgroup G := (f.comp SemidirectProduct.inl).range
  let p : P →* Q := (f.comp SemidirectProduct.inl).rangeRestrict
  have hp : Function.Surjective p := MonoidHom.rangeRestrict_surjective _
  let b : A →* G := f.comp SemidirectProduct.inr
  let : Q.Normal := by
    have hn : (SemidirectProduct.inl : P →* S).range.Normal := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      infer_instance
    change ((f.comp SemidirectProduct.inl).range).Normal
    rw [MonoidHom.range_comp]
    exact hn.map f hf
  let ψ : A →* MulAut Q := (MulAut.conjNormal : G →* MulAut Q).comp b
  have hequiv : ∀ a z, p (φ a z) = ψ a (p z) := by
    intro a z
    apply Subtype.ext
    change f (SemidirectProduct.inl (φ a z)) =
      f (SemidirectProduct.inr a) * f (SemidirectProduct.inl z) *
        (f (SemidirectProduct.inr a))⁻¹
    rw [SemidirectProduct.inl_aut]
    simp
  let σG : Representation (ZMod 2) G W := quotientOfLEKer σ σ.ker le_rfl
  have hσG : Function.Injective σG :=
    (QuotientGroup.injective_lift_iff σ.ker σ le_rfl).mpr rfl
  have hψ : Function.Injective ψ := by
    apply prime_action_injective_of_moving hA
    obtain ⟨a, z, hz⟩ := hmoving
    refine ⟨a, p z, ?_⟩
    intro heq
    apply hz
    have heq' : p (φ a z) = p z := (hequiv a z).trans heq
    exact congrArg (fun x : Q => σG x) heq'
  have hb : Function.Injective b := by
    intro a c heq
    apply hψ
    exact congrArg (MulAut.conjNormal : G →* MulAut Q) heq
  have hQ : IsPGroup q Q := hP.of_surjective p hp
  have hB : IsPGroup r b.range :=
    (IsPGroup.of_card (n := 1) (by simpa using hA)).of_surjective
      b.rangeRestrict b.rangeRestrict_surjective
  have hdis : Disjoint Q b.range := IsPGroup.disjoint_of_ne q r hqr Q b.range hQ hB
  let F : SemidirectProduct Q A ψ →* G :=
    SemidirectProduct.lift Q.subtype b (by intro a; ext z; rfl)
  have hF : Function.Injective F := by
    intro x y hxy
    have he : (x.left, b.rangeRestrict x.right) = (y.left, b.rangeRestrict y.right) :=
      Subgroup.mul_injective_of_disjoint hdis hxy
    apply SemidirectProduct.ext
    · exact congrArg Prod.fst he
    · apply hb
      exact congrArg (fun t : Q × b.range => (t.2 : G)) he
  have hFsurj : Function.Surjective F := by
    intro g
    obtain ⟨s, rfl⟩ := hf g
    refine ⟨⟨p s.left, s.right⟩, ?_⟩
    change f (SemidirectProduct.inl s.left) * f (SemidirectProduct.inr s.right) = f s
    rw [← map_mul, SemidirectProduct.inl_left_mul_inr_right]
  have hminQ : IsMinimalAction ψ := hmin.of_surjective p hp hequiv
  have hirrG : σG.IsIrreducible :=
    (quotientOfLEKer_irreducible_iff σ σ.ker le_rfl).mpr hirr
  have hirrF : IsIrreducible (σG.comp F) :=
    (irreducible_comp_surjective_iff F hFsurj σG).mpr hirrG
  obtain ⟨v, hv, hvA⟩ :=
    hfixed Q A W hQ hA ψ hψ hminQ (σG.comp F) hirrF (hσG.comp hF)
  refine ⟨v, hv, fun a => ?_⟩
  have he := hvA a
  simp only [MonoidHom.comp_apply, F, SemidirectProduct.lift_inr, σG, b, f] at he
  rw [quotientOfLEKer_apply] at he
  exact he

end Representation.PrimeFixedPointCentralization
