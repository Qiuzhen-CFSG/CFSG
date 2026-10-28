module
public import Stellmacher.LaterDefs
public import Theory.GroupAction.NormalizingFixedPoints
public import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# Ambient normalization of quotient-module fixed subgroups

For a quotient-module witness on V, let R lie in its ambient actor subgroup.
If the quotient image of R normalizes F, then R normalizes the image in the
ambient group of the F-fixed subgroup of V. No additional finiteness,
commutativity or coprimality hypotheses are needed.

The normalizing-actor theorem makes the fixed subgroup invariant under the
quotient image of R. The witness's explicit conjugation compatibility
transfers this invariance through V's subtype map. Applying forward stability
to an actor and its inverse gives the ambient normalizer membership.
The exact supplied action instance is retained throughout.

This elementary transfer is used for the relative odd fixed complement in
Stellmacher (9.1), Journal of Algebra 190 (1997), p.47. The witness belongs to
the campaign's shared definitions, so the adapter is placed at that layer.
-/

namespace Stellmacher.Later
universe u

public theorem QuotientModuleWitness.le_normalizer_fixedPoints_map
    {G : Type u} [Group G] {A B V : Subgroup G}
    (w : QuotientModuleWitness A B V) (R : Subgroup G) (hRA : R ≤ A)
    (F : let _ := w.groupX; Subgroup w.X) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom V w.action
    (R.subgroupOf A).map w.projection ≤ Subgroup.normalizer (F : Set w.X) →
      R ≤ Subgroup.normalizer
        (((FixedPoints.subgroup F V).map V.subtype : Subgroup G) : Set G) := by
  let _ := w.groupX
  let _ := MulDistribMulAction.compHom V w.action
  change (R.subgroupOf A).map w.projection ≤ Subgroup.normalizer (F : Set w.X) →
    R ≤ Subgroup.normalizer
      (((FixedPoints.subgroup F V).map V.subtype : Subgroup G) : Set G)
  intro hn
  let I := (R.subgroupOf A).map w.projection
  let C := FixedPoints.subgroup F V
  let _ : IsInvariant I V C := fixedPoints_isInvariant_of_normalizing_actor I F hn
  have hforward : ∀ r ∈ R, ∀ x ∈ C.map V.subtype,
      r * x * r⁻¹ ∈ C.map V.subtype := by
    intro r hr x hx
    obtain ⟨v,hv,rfl⟩ := hx
    let rA : A := ⟨r,hRA hr⟩
    let rI : I := ⟨w.projection rA,Subgroup.mem_map_of_mem w.projection hr⟩
    refine ⟨rI • v,(IsInvariant.invariant (A := I) (G := V) (H := C) rI v).mp hv,?_⟩
    exact w.action_compatible rA v
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward r hr x
  · intro hx
    have hh := hforward r⁻¹ (R.inv_mem hr) (r*x*r⁻¹) hx
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,
      inv_mul_cancel,mul_one] using hh

end Stellmacher.Later
