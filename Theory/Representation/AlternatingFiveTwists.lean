module
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.AlternatingFive
public import Theory.Alternating.Aut

/-!
# Automorphism twists of the two binary A₅ models

Every automorphism of A₅ is induced by S₅. The deleted module extends by
coordinate permutations, and the natural SL₂(4) module extends by the
marked semilinear S₅ on its five field lines. Thus each model is equivalent
to every automorphism twist, with actual binary linear intertwiners.

Source: Aschbacher–Smith, G.9.3 and I.1.6(3), used in D.3.6,
combined manuscript, printed pp.354,408 and196.
-/

@[expose] public section
open scoped MatrixGroups
namespace Representation.AlternatingFiveTwists
open SL2FourNatural SL2FourNatural.SemilinearNormalizer

theorem concrete_natural_twist (a : MulAut SL) :
    ∃ c : V ≃ₗ[ZMod 2] V, ∀ g v, c (action g v) = action (a g) (c v) := by
  let e := alternatingFiveEquiv
  let φ := e.symm.trans (a.trans e)
  obtain ⟨p, hp⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide)).surjective φ
  let C := symmetricFiveEquiv.symm p
  refine ⟨C.val, ?_⟩
  intro g v
  let A : specialField := ⟨action g, (show action.range ≤ specialField from le_sup_left) ⟨g, rfl⟩⟩
  let B : specialField := ⟨action (a g), (show action.range ≤ specialField from le_sup_left) ⟨a g, rfl⟩⟩
  have hh : C * A * C⁻¹ = B := by
    apply symmetricFiveEquiv.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
      symmetricFiveEquiv_special_apply, symmetricFiveEquiv_special_apply]
    have he := congrArg (fun f : MulAut (alternatingGroup (Fin 5)) =>
      (f (e g) : Equiv.Perm (Fin 5))) hp
    change p * (e g).val * p⁻¹ = (e (a (e.symm (e g)))).val at he
    simpa only [e.symm_apply_apply, e, alternatingFiveEquiv_apply] using he
  have hlin : C.val * action g = action (a g) * C.val :=
    mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)
  exact LinearEquiv.congr_fun hlin v

theorem natural_twist (a : MulAut (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))) :
    ∃ c : (Fin 2 → GaloisField 2 2) ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2),
      ∀ g v, c (SL2.BinarySmall.natural g v) = SL2.BinarySmall.natural (a g) (c v) := by
  let e := standardGroupEquiv
  let F := standardVectorEquiv
  obtain ⟨c, hc⟩ := concrete_natural_twist (e.trans (a.trans e.symm))
  refine ⟨F.symm.trans (c.trans F), ?_⟩
  intro g v
  obtain ⟨g, rfl⟩ := e.surjective g
  obtain ⟨v, rfl⟩ := F.surjective v
  change F (c (F.symm (specialLinearNatural 2 (e g) (F v)))) =
    specialLinearNatural 2 (a (e g)) (F (c (F.symm (F v))))
  rw [←standard_equivariant, F.symm_apply_apply, F.symm_apply_apply, hc,
    standard_equivariant]
  change specialLinearNatural 2 (e (e.symm (a (e g)))) (F (c v)) = _
  rw [e.apply_symm_apply]

theorem deleted_twist (a : MulAut (alternatingGroup (Fin 5))) :
    ∃ c : BinaryPermutation.natural (Fin 5) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 5), ∀ g v,
      c (OrthogonalFourMinus.AlternatingFive.alternatingRepresentation g v) =
        OrthogonalFourMinus.AlternatingFive.alternatingRepresentation (a g) (c v) := by
  obtain ⟨p, hp⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide)).surjective a
  let σ := BinaryPermutation.naturalRepresentation (Fin 5)
  let C := LinearEquiv.ofBijective (σ p) (σ.apply_bijective p)
  refine ⟨C, ?_⟩
  intro g v
  have he : (a g : Equiv.Perm (Fin 5)) = p * g.val * p⁻¹ :=
    (congrArg (fun f : MulAut (alternatingGroup (Fin 5)) => (f g).val) hp).symm
  change σ p (σ g.val v) = σ (a g).val (σ p v)
  rw [he]
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

end Representation.AlternatingFiveTwists
