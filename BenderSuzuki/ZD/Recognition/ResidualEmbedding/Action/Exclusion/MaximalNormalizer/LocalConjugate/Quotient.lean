module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Basic

/-!
# The distinguished local quotient

Here `N°` is literally the closure of the distinguished elements inside
`N_G(Q)`. The quotient construction uses the pullback of its odd core to
`M₁ = M ∩ N°`. Identifying that pullback with the whole odd core requires
`O₂'(N°) ≤ M₁`; the local structure argument must prove this separately.
The inverse image defining `M₂` is normal in `M₁` and has precisely the
specified image in this quotient.

Source: GLS, Volume 4, Chapter 2, (7E)--(7G). The quotient bookkeeping is
adapted from `BenderSuzuki.SE.Section7Final`, with the distinguished closure
in place of the full involution core.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1

/-- The distinguished closure inside the local normalizer. -/
@[expose] public def actionLocalNCore
    {X : Type*} [Group X] (Z : Set X) (Q : Subgroup X) :
    Subgroup (Subgroup.normalizer (Q : Set X)) :=
  Subgroup.closure ((Subgroup.normalizer (Q : Set X)).subtype ⁻¹' Z)

/-- The actual intersection `M ∩ N°`, internal to the distinguished closure. -/
@[expose] public def actionLocalM1
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) :
    Subgroup (actionLocalNCore Z Q) :=
  (M.comap (Subgroup.normalizer (Q : Set X)).subtype).comap
    (actionLocalNCore Z Q).subtype

/-- The odd core pulled back to `M₁`. The containment theorem is needed before
this can be identified with the whole odd core. -/
@[expose] public def actionLocalO1
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) :
    Subgroup (actionLocalM1 Z M Q) :=
  (pPrimeCore 2 (actionLocalNCore Z Q)).comap (actionLocalM1 Z M Q).subtype

public instance actionLocalO1_normal
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) :
    (actionLocalO1 Z M Q).Normal :=
  Subgroup.Normal.comap (inferInstance : (pPrimeCore 2 (actionLocalNCore Z Q)).Normal)
    (actionLocalM1 Z M Q).subtype

/-- Containment identifies the quotient kernel with the full local odd core. -/
public theorem actionLocalO1_map_eq
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X)
    (hO : pPrimeCore 2 (actionLocalNCore Z Q) ≤ actionLocalM1 Z M Q) :
    (actionLocalO1 Z M Q).map (actionLocalM1 Z M Q).subtype =
      pPrimeCore 2 (actionLocalNCore Z Q) := by
  change ((pPrimeCore 2 (actionLocalNCore Z Q)).comap
    (actionLocalM1 Z M Q).subtype).map (actionLocalM1 Z M Q).subtype = _
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.mpr hO]

/-- The right side of `(7F)`, namely `Omega₁(O₂(M₁/O₂'(N°)))`. -/
@[expose] public def actionLocalM2Quotient
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) :
    Subgroup ((actionLocalM1 Z M Q) ⧸
      (actionLocalO1 Z M Q)) :=
  let P := pCore 2 ((actionLocalM1 Z M Q) ⧸
    (actionLocalO1 Z M Q))
  (omega₁ (G := P) (p := 2)).map P.subtype

public instance actionLocalM2Quotient_characteristic
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) :
    (actionLocalM2Quotient Z M Q).Characteristic := by
  let G := (actionLocalM1 Z M Q) ⧸ (actionLocalO1 Z M Q)
  let P := pCore 2 G
  have : P.Characteristic := pCore_characteristic
  have : (omega₁ (G := P) (p := 2)).Characteristic :=
    omega₁_characteristic P
  have hchar : ((omega₁ (G := P) (p := 2)).map P.subtype).Characteristic :=
    characteristic_map_subtype_of_characteristic P
      (omega₁ (G := P) (p := 2))
  simpa [actionLocalM2Quotient, G, P] using
    hchar

public instance actionLocalM2Quotient_normal
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) :
    (actionLocalM2Quotient Z M Q).Normal := by
  infer_instance

/-- The inverse image of `Omega₁(O₂(M₁/O₁))` in `M₁`. -/
@[expose] public def actionLocalM2
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) :
    Subgroup (actionLocalM1 Z M Q) :=
  (actionLocalM2Quotient Z M Q).comap
    (QuotientGroup.mk' (actionLocalO1 Z M Q))

public instance actionLocalM2_normal
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) :
    (actionLocalM2 Z M Q).Normal := by
  exact Subgroup.Normal.comap (actionLocalM2Quotient_normal Z M Q)
    (QuotientGroup.mk' (actionLocalO1 Z M Q))

/-- Equation `(7F)` in quotient form. -/
public theorem actionLocalM2_quotient_image
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) :
    (actionLocalM2 Z M Q).map
        (QuotientGroup.mk' (actionLocalO1 Z M Q)) =
      actionLocalM2Quotient Z M Q := by
  exact Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (actionLocalO1 Z M Q)) _

/-- Equation `(7G)`: `M₂` is normal in `M₁`. -/
public theorem actionLocalM2_relative_normal
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) :
    (actionLocalM2 Z M Q).Normal :=
  actionLocalM2_normal Z M Q

/-- The canonical quotient-defined subgroup `M₂` in the original group. -/
@[expose] public def actionLocalM2InG
    {X : Type*} [Group X] (Z : Set X) (M Q : Subgroup X) : Subgroup X :=
  (((actionLocalM2 Z M Q).map (actionLocalM1 Z M Q).subtype).map
    (actionLocalNCore Z Q).subtype).map (Subgroup.normalizer (Q : Set X)).subtype

end BenderSuzuki.ZD
