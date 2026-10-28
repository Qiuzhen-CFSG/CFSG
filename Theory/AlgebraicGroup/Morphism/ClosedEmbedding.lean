module

public import Theory.AlgebraicGroup.Morphism.ClosedImage

universe u

/-! Closed embeddings of affine algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A faithful algebraic-group morphism is an isomorphism onto its closed
image when every source coordinate is the pullback of a target polynomial
function. -/
public theorem Morphism.iso_imageClosedSubgroup_of_coordinate_preimage
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hinjective : Function.Injective f.onPoints)
    (hcoordinate : ∀ c : G.Coordinates,
      ∃ q : Variety.PolynomialFunction H,
        Variety.PolynomialFunction.pullback f.toVariety q =
          Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X c)) :
    let I := f.imageClosedSubgroup
    letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
    ∃ e : AlgebraicGroup.Iso G I.carrierVariety,
      e.hom = f.codRestrictClosedSubgroup I (fun y ↦ ⟨y, rfl⟩) := by
  dsimp
  let I := f.imageClosedSubgroup
  let : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  let hmap : ∀ x, f.onPoints x ∈ I.toSubgroup := fun x ↦ ⟨x, rfl⟩
  let r : AlgebraicGroup.Morphism G I.carrierVariety :=
    f.codRestrictClosedSubgroup I hmap
  let surjective : Function.Surjective r.onPoints :=
    f.codRestrictImageClosedSubgroup_surjective hmap
  let inversePoint : Variety.Point I.carrierVariety → Variety.Point G :=
    fun y ↦ Classical.choose (surjective y)
  have inversePoint_spec (y : Variety.Point I.carrierVariety) :
      r.onPoints (inversePoint y) = y :=
    Classical.choose_spec (surjective y)
  let inverse : AlgebraicGroup.Morphism I.carrierVariety G :=
    { toVariety :=
        { toFun := inversePoint
          regular := by
            intro c
            obtain ⟨q, hq⟩ := hcoordinate c
            let qI : Variety.PolynomialFunction I.carrierVariety :=
              Variety.PolynomialFunction.pullback I.inclusion.toVariety q
            obtain ⟨p, hp⟩ := qI.representedBy
            refine ⟨p, ?_⟩
            intro y
            have hqy : qI y =
                Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X c)
                  (inversePoint y) := by
              have hq' := congrArg
                (fun a : Variety.PolynomialFunction G ↦ a (inversePoint y)) hq
              change q (f.onPoints (inversePoint y)) =
                Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X c)
                  (inversePoint y) at hq'
              change q (I.inclusion.onPoints y) = _
              have hinclusion := congrArg I.inclusion.onPoints
                (inversePoint_spec y)
              rw [Morphism.codRestrictClosedSubgroup_inclusion_apply] at hinclusion
              rw [← hinclusion]
              exact hq'
            have hpy : qI y = evalPolynomial y.val p := hp y
            rw [hpy] at hqy
            simpa [Variety.PolynomialFunction.ofPolynomial,
              Variety.PolynomialFunction.toFun, evalPolynomial] using hqy.symm }
      map_one := by
        apply hinjective
        have hone := congrArg I.inclusion.onPoints
          (inversePoint_spec (1 : Variety.Point I.carrierVariety))
        simpa [r, Morphism.codRestrictClosedSubgroup_inclusion_apply] using hone
      map_mul := by
        intro x y
        apply hinjective
        have hx : f.onPoints (inversePoint x) = I.inclusion.onPoints x := by
          simpa [r, Morphism.codRestrictClosedSubgroup_inclusion_apply] using
            congrArg I.inclusion.onPoints (inversePoint_spec x)
        have hy : f.onPoints (inversePoint y) = I.inclusion.onPoints y := by
          simpa [r, Morphism.codRestrictClosedSubgroup_inclusion_apply] using
            congrArg I.inclusion.onPoints (inversePoint_spec y)
        calc
          f.onPoints (inversePoint (x * y)) =
              I.inclusion.onPoints (x * y) := by
            simpa [r, Morphism.codRestrictClosedSubgroup_inclusion_apply] using
              congrArg I.inclusion.onPoints (inversePoint_spec (x * y))
          _ = I.inclusion.onPoints x * I.inclusion.onPoints y :=
            (I.inclusion.map_mul x y).symm
          _ = f.onPoints (inversePoint x * inversePoint y) := by
            rw [MonoidHom.map_mul f.onPoints, hx, hy] }
  have inverse_comp (x : Variety.Point G) :
      inverse.onPoints (r.onPoints x) = x := by
    apply hinjective
    have h := congrArg I.inclusion.onPoints
      (inversePoint_spec (r.onPoints x))
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply] at h
    exact h
  have comp_inverse (y : Variety.Point I.carrierVariety) :
      r.onPoints (inverse.onPoints y) = y := by
    apply I.inclusion_injective
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    have h := congrArg I.inclusion.onPoints (inversePoint_spec y)
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply] at h
    exact h
  let e : AlgebraicGroup.Iso G I.carrierVariety :=
    { hom := r
      inv := inverse
      hom_inv_id := inverse_comp
      inv_hom_id := comp_inverse }
  exact ⟨e, rfl⟩

end Theory.AlgebraicGroup
