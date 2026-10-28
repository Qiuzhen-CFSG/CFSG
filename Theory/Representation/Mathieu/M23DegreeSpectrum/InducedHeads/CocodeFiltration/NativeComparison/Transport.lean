module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison.Transversal

/-!
# Native coinduction evaluated on the inverse saved transversal

The orbit of point 9 proves injectivity of evaluation: every group element
is a subgroup correction times an inverse representative. The known dimension
then gives a linear equivalence. Intertwining with the original right-coset
action uses the actual coinduction equivalence and the checked correction
identity, so no choice of `Quotient.out` is identified with saved data.

Source application: Guralnick--Malle I, Proposition 5.1, M23 paragraph.
-/

open Sporadic.Mathieu
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison
@[expose] public noncomputable section

abbrev Coinduced := Representation.coindV Models.pointGroup.subtype
  (Models.pointAction canonicalMarking false)

/-- Evaluate the actual coinduced function at inverse GAP representatives. -/
def evaluate : Coordinates.Space false →ₗ[ZMod 2] (Fin 23 → Models.Space false) where
  toFun v i := ((Coordinates.coindEquiv canonicalMarking false).symm v).val (transversal i)⁻¹
  map_add' u v := by
    funext i
    simp only [map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' c v := by
    funext i
    simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]

theorem evaluate_injective : Function.Injective evaluate := by
  intro u v huv
  apply (Coordinates.coindEquiv canonicalMarking false).symm.toLinearEquiv.injective
  apply Subtype.ext
  funext g
  obtain ⟨i, hi⟩ := orbitPoint_bijective.surjective (g.val.symm 9)
  have hs : g * transversal i ∈ Models.pointGroup := by
    change g.val ((transversal i).val 9) = 9
    rw [transversal_apply]
    change g.val (orbitPoint i) = 9
    rw [hi, _root_.Equiv.apply_symm_apply]
  let h : Models.pointGroup := ⟨g * transversal i, hs⟩
  have hf (f : Coinduced) : f.val g =
      Models.pointAction canonicalMarking false h (f.val (transversal i)⁻¹) := by
    simpa only [h, Subgroup.coe_mk, Subgroup.subtype_apply, mul_inv_cancel_right] using
      f.property h (transversal i)⁻¹
  rw [hf, hf]
  exact congrArg _ (congrFun huv i)

/-- Inverse-transversal evaluation is a genuine linear equivalence. -/
def evaluationEquiv : Coordinates.Space false ≃ₗ[ZMod 2] (Fin 23 → Models.Space false) := by
  letI : Fintype Coordinates.Cosets := Fintype.ofFinite _
  exact evaluate.linearEquivOfInjective evaluate_injective (by
    rw [Coordinates.finrank_space, Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    change 230 = 23 * Module.finrank (ZMod 2) MathieuCode.M22Cocode
    rw [MathieuCode.finrank_m22Cocode])

theorem evaluationEquiv_apply (v : Coordinates.Space false) (i : Fin 23) :
    evaluationEquiv v i =
      ((Coordinates.coindEquiv canonicalMarking false).symm v).val (transversal i)⁻¹ := rfl

/-- The block equation retains the subgroup correction, with its exact direction. -/
theorem evaluation_generator (k : Fin 2) (v : Coordinates.Space false) (i : Fin 23) :
    evaluationEquiv (canonicalCocodeAction (actor k) v) (blockPerm k i) =
      Models.pointAction canonicalMarking false (correction k i) (evaluationEquiv v i) := by
  rw [evaluationEquiv_apply, evaluationEquiv_apply]
  have he := Representation.IntertwiningMap.isIntertwining _ _
    (Coordinates.coindEquiv canonicalMarking false).symm.toIntertwiningMap (actor k) v
  have heval := congrArg (fun f : Coinduced => f.val (transversal (blockPerm k i))⁻¹) he
  rw [show (((Coordinates.coindEquiv canonicalMarking false).symm
      (canonicalCocodeAction (actor k) v)).val (transversal (blockPerm k i))⁻¹) =
      ((Representation.coind Models.pointGroup.subtype
        (Models.pointAction canonicalMarking false) (actor k))
        ((Coordinates.coindEquiv canonicalMarking false).symm v)).val
        (transversal (blockPerm k i))⁻¹ from heval]
  change ((Coordinates.coindEquiv canonicalMarking false).symm v).val
    ((transversal (blockPerm k i))⁻¹ * actor k) = _
  rw [← correction_mul_inverse]
  exact ((Coordinates.coindEquiv canonicalMarking false).symm v).property
    (correction k i) (transversal i)⁻¹

end
end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison
