module
public import Theory.GroupTheory.OddSemilinearModelLift

/-!
# Odd semilinear lifts into an actual ambient group

Let D be a finite invariant subgroup of an ambient group X equipped with
the specified coefficient action α. Under the central two-kernel and odd
complement hypotheses of the semilinear model lift, the original finite
group embeds into X semidirect A, with the prescribed D-valued linear
coordinates and coefficient map. The projective-equivariance and fixed
Sylow hypotheses are expressed pointwise in X, so callers retain their
actual matrix actions without constructing a separate public action on D.

Privately restrict each automorphism to D using the membership equivalence.
The pointwise hypotheses then give exactly the equivariance and Sylow
fixation required by the established odd-complement lift. Compose its map
into D semidirect A with the semidirect homomorphism induced by the subtype
inclusion and identity on A. Injectivity follows on the two coordinates;
the defining linear and coefficient values are preserved by this inclusion.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp27–28.
This generic transfer lets the linear and unitary applications use their
original ambient matrix coefficient actions. No matrix recognition or
new public restricted-action instance is assumed.
-/

namespace Subgroup

private def restrictAutomorphisms {X A : Type*} [Group X] [Group A]
    (D : Subgroup X) (α : A →* MulAut X)
    (hD : ∀ a x, α a x ∈ D ↔ x ∈ D) : A →* MulAut D where
  toFun a := {
    toFun := fun x => ⟨α a x.val, (hD a x.val).mpr x.property⟩
    invFun := fun x => ⟨(α a).symm x.val, (hD a ((α a).symm x.val)).mp (by simp only [MulEquiv.apply_symm_apply]; exact x.property)⟩
    left_inv := fun x => Subtype.ext ((α a).symm_apply_apply x.val)
    right_inv := fun x => Subtype.ext ((α a).apply_symm_apply x.val)
    map_mul' := fun x y => Subtype.ext ((α a).map_mul x.val y.val) }
  map_one' := by ext x; exact congrArg (fun f : MulAut X => f x.val) α.map_one
  map_mul' a b := by ext x; exact congrArg (fun f : MulAut X => f x.val) (α.map_mul a b)

/-- Lift an odd complement into the specified ambient semidirect product,
using pointwise equivariance on its actual invariant model subgroup. -/
public theorem exists_injective_semilinear_subgroup_lift_of_odd_complement
    {H X Q A : Type*} [Group H] [Finite H] [Group X]
    [Group Q] [Group A] (D : Subgroup X) [Finite D]
    (L E : Subgroup H) [L.Normal] (hcomp : L.IsComplement' E)
    (hodd : Odd (Nat.card E)) (α : A →* MulAut X)
    (hD : ∀ a x, α a x ∈ D ↔ x ∈ D) (β : A →* MulAut Q)
    (eL : L ≃* D) (c : E →* A) (hc : Function.Injective c)
    (q : D →* Q)
    (hq : ∀ (a : A) (x y : D), y.val = α a x.val → q y = β a (q x))
    (hqtwo : IsPGroup 2 q.ker)
    (hZ : (q.ker.comap eL.toMonoidHom).map L.subtype ≤ center H)
    (f : H →* Q ⋊[β] A)
    (hfL : ∀ l : L, f l = SemidirectProduct.inl (q (eL l)))
    (hfE : ∀ e : E, f e = SemidirectProduct.inr (c e))
    (T : Sylow 2 D) (hT : ∀ (e : E) (t : T), α (c e) t.val.val = t.val.val)
    (L0 : Subgroup L)
    (hno : ∀ N : Subgroup L0, N.Normal → N.index ≠ 2)
    (hgen : L0 ⊔ (T : Subgroup D).comap eL.toMonoidHom = ⊤) :
    ∃ F : H →* X ⋊[α] A, Function.Injective F ∧
      (∀ l : L, F l = SemidirectProduct.inl (eL l).val) ∧
      (∀ e : E, F e = SemidirectProduct.inr (c e)) := by
  let αD := restrictAutomorphisms D α hD
  have hqD (a : A) (d : D) : q (αD a d) = β a (q d) := hq a d (αD a d) rfl
  have hTD (e : E) (t : T) : αD (c e) t.val = t.val := Subtype.ext (hT e t)
  obtain ⟨F0, hF0, hF0L, hF0E⟩ := exists_injective_semilinear_lift_of_odd_complement
    L E hcomp hodd αD β eL c hc q hqD hqtwo hZ f hfL hfE T hTD L0 hno hgen
  have hmap (a : A) : D.subtype.comp (αD a).toMonoidHom =
      (α ((MonoidHom.id A) a)).toMonoidHom.comp D.subtype := rfl
  let i : D ⋊[αD] A →* X ⋊[α] A := SemidirectProduct.map D.subtype (MonoidHom.id A) hmap
  have hi : Function.Injective i := by
    intro x y h
    apply SemidirectProduct.ext
    · exact Subtype.ext (congrArg SemidirectProduct.left h)
    · exact congrArg (fun z : X ⋊[α] A => z.right) h
  refine ⟨i.comp F0, hi.comp hF0, ?_, ?_⟩
  · intro l
    change i (F0 l) = _
    rw [hF0L]
    exact SemidirectProduct.map_inl _ _ _ _
  · intro e
    change i (F0 e) = _
    rw [hF0E]
    exact SemidirectProduct.map_inr _ _ _ _
end Subgroup
