module

public import Theory.Character.Induction

/-!
# Transitivity of character induction

Induction through a subgroup agrees with induction from the image of the
nested subgroup in the ambient group. Pairing with an arbitrary invariant
function reduces this to Frobenius reciprocity twice and a change of variables
along the subgroup equivalence. Nondegeneracy then gives equality.

This is the usual transitivity theorem for induced characters; see Serre,
*Linear Representations of Finite Groups*, §7.1. It holds here even when the
function on the smallest subgroup is not conjugacy invariant.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Group G] [Fintype G]

/-- Induction through a subgroup equals induction from the ambient image of
its subgroup. The function is transported by the canonical group equivalence. -/
theorem inducedClassFunction_trans (H : Subgroup G) (K : Subgroup H)
    (f : ClassFunction K) :
    inducedClassFunction H (inducedClassFunction K f) =
      inducedClassFunction (K.map H.subtype)
        (fun x => f ((K.equivMapOfInjective H.subtype H.subtype_injective).symm x)) := by
  classical
  let e := K.equivMapOfInjective H.subtype H.subtype_injective
  apply IsClassFunction.eq_of_scalarProduct_eq
    (inducedClassFunction_isClassFunction H _)
    (inducedClassFunction_isClassFunction (K.map H.subtype) _)
  intro ψ hψ
  have hrestrict : IsClassFunction (fun x : H => ψ (x : G)) := by
    intro x g
    exact hψ x g
  calc
    scalarProduct G (inducedClassFunction H (inducedClassFunction K f)) ψ =
        scalarProduct H (inducedClassFunction K f) (fun x : H => ψ (x : G)) :=
      scalarProduct_inducedClassFunction H _ hψ
    _ = scalarProduct K f (fun x : K => ψ (x : G)) :=
      scalarProduct_inducedClassFunction K f hrestrict
    _ = scalarProduct G (inducedClassFunction (K.map H.subtype)
        (fun x => f (e.symm x))) ψ := ?_
  rw [scalarProduct_inducedClassFunction (K.map H.subtype) _ hψ]
  unfold scalarProduct
  rw [Nat.card_congr e.toEquiv]
  congr 1
  apply Fintype.sum_equiv e.toEquiv
  intro x
  simp [e]
