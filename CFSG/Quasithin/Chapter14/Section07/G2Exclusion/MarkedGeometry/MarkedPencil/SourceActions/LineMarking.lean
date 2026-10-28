module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.Points
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking.SylowTransport
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking.Quotient

/-!
# Marking the source line from its local actions

For the actual natural and trace-zero Weyl actions of G₂(2), an order-four
subspace invariant under a Sylow two-subgroup of G₂(2)′ is recognized using
three square actions. In the Weyl case its equality with the L₁-commutator
span removes the scalar-coordinate obstruction. The resulting octonion
plane has zero products, so it defines a genuine doubly singular line.

The source applications pull V back from the literal quotient
U/(V₁.subgroupOf U), derive its order, invariance and commutator span from
the earlier local identities, and construct its line marking. The Weyl
application then supplies the previously missing line premise of
`SourceActions.weyl_source_point_and_pencil`, proving clauses
(1)–(3) together. No singularity or geometric marking is an input.

The module-identification owner of 14.7.54 supplies the actual equivariant
natural/Weyl equivalence and actor maps, with the image of T containing an
actual derived Sylow. Earlier Section 14.7 supplies the orders four and
two, V₂ ≤ V ≤ U, [V,L₁]V₁ = V, and the stated relative normalizations.
These genuine earlier-source premises remain explicit; their final
instantiation belongs to the Section 14.7 source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 14.7.55,
printed p.1066, PDF p.1083. Coordinates and models use the attributed
ATLAS port (LICENSES/ATLAS.txt); no additional ATLAS source is copied.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion Atlas.G2.Natural
open Atlas.G2.BinaryParabolicPair
open Representation.BinaryOffender
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

open Subgroup

abbrev W := TraceZero (ZMod 2)
abbrev O := Carrier (ZMod 2)
@[expose] def carrierPlane (P : Submodule (ZMod 2) W) : Submodule (ZMod 2) O := P.map (TraceZero (ZMod 2)).subtype
lemma carrierPlane_card (P : Submodule (ZMod 2) W) : Nat.card (carrierPlane P) = Nat.card P := by
  simpa [carrierPlane] using (Nat.card_congr (Submodule.equivMapOfInjective
    (TraceZero (ZMod 2)).subtype (TraceZero (ZMod 2)).subtype_injective P).toEquiv).symm
theorem carrierPlane_trace (P : Submodule (ZMod 2) W) : traceRestriction (carrierPlane P) = P := by
  ext x
  constructor
  · intro hx
    change x.val ∈ P.map (TraceZero (ZMod 2)).subtype at hx
    rcases hx with ⟨z,hz,hy⟩
    have he : z = x := Subtype.ext hy
    simpa [he] using hz
  · intro hx
    change x.val ∈ P.map (TraceZero (ZMod 2)).subtype
    exact ⟨x,hx,rfl⟩
theorem carrierPlane_product (P : Submodule (ZMod 2) W)
    (hzero : ∀ x ∈ P, ∀ y ∈ P, mul x.val y.val = 0) :
    ∀ x ∈ carrierPlane P, ∀ y ∈ carrierPlane P, mul x y = 0 := by
  intro x hx y hy
  change x ∈ P.map (TraceZero (ZMod 2)).subtype at hx
  change y ∈ P.map (TraceZero (ZMod 2)).subtype at hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  simpa using hzero a ha b hb
theorem line_of_zeroProduct (P : Submodule (ZMod 2) W)
    (hcard : Nat.card P = 4)
    (hzero : ∀ x ∈ P, ∀ y ∈ P, mul x.val y.val = 0) :
    ∃ L : ZeroProductLine (ZMod 2), weylMap.line L = P := by
  have hcard' : Nat.card (carrierPlane P) = 4 := (carrierPlane_card P).trans hcard
  have hdim : Module.finrank (ZMod 2) (carrierPlane P) = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    simpa [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] using hcard'
  let L : ZeroProductLine (ZMod 2) :=
    ⟨carrierPlane P, hdim, carrierPlane_product P hzero⟩
  refine ⟨L, ?_⟩
  unfold SingularMap.line SingularMap.image
  rw [carrierPlane_trace]
  change P.map LinearMap.id = P
  exact Submodule.map_id P


/-- The conditional geometric bridge: `himage` identifies the chosen subspace
with the literal quotient image. The local-action application below derives
zero products from the earlier commutator and normalization identities. -/
theorem weyl_source_point_and_pencil_of_zeroProduct
    {Q : Type*} [Group Q]
    (U V₁ V₂ V : Subgroup Q) [(V₁.subgroupOf U).Normal]
    (e : Multiplicative (TraceZero (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (hcard : Nat.card ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 2)
    (hV₂ : V₂ ≤ V) (P : Submodule (ZMod 2) (TraceZero (ZMod 2)))
    (hPcard : Nat.card P = 4)
    (hzero : ∀ x ∈ P, ∀ y ∈ P, Atlas.SplitOctonion.mul x.val y.val = 0)
    (himage : (V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      P.toAddSubgroup.toSubgroup.map e.toMonoidHom) :
    ∃ L : ZeroProductLine (ZMod 2),
      (∃ p : SingularPoints (ZMod 2),
        (weylQuotientGeometry (V₁.subgroupOf U) e).point p =
          (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) ∧
        pointOnLine p L) ∧
      Nat.card (quotientPencil (weylQuotientGeometry (V₁.subgroupOf U) e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) = 3 ∧
      Nat.card (quotientPencilSpan (weylQuotientGeometry (V₁.subgroupOf U) e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) = 8 := by
  obtain ⟨L, hL⟩ := line_of_zeroProduct P hPcard hzero
  have hV : (V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (weylQuotientGeometry (V₁.subgroupOf U) e).line L := by
    rw [himage]
    change P.toAddSubgroup.toSubgroup.map e.toMonoidHom =
      (weylMap.line L).toAddSubgroup.toSubgroup.map e.toMonoidHom
    rw [hL]
  exact ⟨L, weyl_source_point_and_pencil U V₁ V₂ V e hcard hV₂ L hV⟩


/-- An order-four Weyl subspace invariant under an actual derived Sylow and
generated by its local action differences is a genuine doubly singular line. -/
theorem weyl_line_of_sylow_commutator
    (P : Submodule (ZMod 2) (TraceZero (ZMod 2))) (hc : Nat.card P = 4)
    (S : Sylow 2 DerivedModel)
    (hP : (S : Subgroup DerivedModel).map DerivedModel.subtype ≤
      subspaceStabilizer (traceZeroAction (ZMod 2)) P)
    (X : Subgroup (Model (ZMod 2)))
    (hX : subspaceCommutator (traceZeroAction (ZMod 2)) P X = P) :
    ∃ L : ZeroProductLine (ZMod 2), weylMap.line L = P :=
  line_of_zeroProduct P hc (weyl_sylow_zeroProduct P hc S hP X hX)

open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil

section Applications
variable {Q : Type*} [Group Q]

/-- Clause 14.7.55(1) in the natural quotient, from the actual T action and
the earlier order-four identity. -/
theorem natural_source_line_of_local_actions
    (U V₁ V T : Subgroup Q) [(V₁.subgroupOf U).Normal]
    (e : Multiplicative (Space (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (hcard : Nat.card ((V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 4)
    (kT : T →* Model (ZMod 2))
    (hnTU : T ≤ normalizer (U : Set Q)) (hnTV : T ≤ normalizer (V : Set Q))
    (hactT : ∀ (t : T) (v : U), action (ZMod 2) (kT t) ((sourceMap U V₁ e v).toAdd) =
      (sourceMap U V₁ e ⟨(t : Q) * v * (t : Q)⁻¹,
        le_normalizer_iff.mp hnTU t t.property v v.property⟩).toAdd)
    (S : Sylow 2 DerivedModel)
    (hS : (S : Subgroup DerivedModel).map DerivedModel.subtype ≤ kT.range) :
    ∃ L : ZeroProductLine (ZMod 2),
      (V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
        (naturalQuotientGeometry (V₁.subgroupOf U) e).line L := by
  obtain ⟨L, hL⟩ := natural_sylow_line (sourcePlane U V₁ V e)
    ((sourcePlane_card U V₁ V e).trans hcard) S
    (hS.trans (sourcePlane_invariant U V₁ V T e _ kT hnTU hnTV hactT))
  refine ⟨L, ?_⟩
  change _ = (naturalMap.line L).toAddSubgroup.toSubgroup.map e.toMonoidHom
  rw [hL, sourcePlane_image]

/-- Clause 14.7.55(1) in the Weyl quotient. Apply with `X = L₁`; the earlier
identity `[V,L₁]V₁ = V` supplies `hlocal`. -/
theorem weyl_source_line_of_local_actions
    (U V₁ V X T : Subgroup Q) [(V₁.subgroupOf U).Normal]
    (e : Multiplicative (TraceZero (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (hcard : Nat.card ((V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 4)
    (hVU : V ≤ U) (hlocal : ⁅V, X⁆ ⊔ V₁ = V)
    (kX : X →* Model (ZMod 2)) (kT : T →* Model (ZMod 2))
    (hnXU : X ≤ normalizer (U : Set Q))
    (hnTU : T ≤ normalizer (U : Set Q)) (hnTV : T ≤ normalizer (V : Set Q))
    (hactX : ∀ (x : X) (v : U), traceZeroAction (ZMod 2) (kX x)
        ((sourceMap U V₁ e v).toAdd) =
      (sourceMap U V₁ e ⟨(x : Q) * v * (x : Q)⁻¹,
        le_normalizer_iff.mp hnXU x x.property v v.property⟩).toAdd)
    (hactT : ∀ (t : T) (v : U), traceZeroAction (ZMod 2) (kT t)
        ((sourceMap U V₁ e v).toAdd) =
      (sourceMap U V₁ e ⟨(t : Q) * v * (t : Q)⁻¹,
        le_normalizer_iff.mp hnTU t t.property v v.property⟩).toAdd)
    (S : Sylow 2 DerivedModel)
    (hS : (S : Subgroup DerivedModel).map DerivedModel.subtype ≤ kT.range) :
    ∃ L : ZeroProductLine (ZMod 2),
      (V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
        (weylQuotientGeometry (V₁.subgroupOf U) e).line L := by
  have hc := (sourcePlane_card U V₁ V e).trans hcard
  obtain ⟨L, hL⟩ := weyl_line_of_sylow_commutator (sourcePlane U V₁ V e) hc S
    (hS.trans (sourcePlane_invariant U V₁ V T e _ kT hnTU hnTV hactT)) kX.range
    (sourcePlane_commutator U V₁ V X e _ kX hVU hnXU hlocal hactX)
  refine ⟨L, ?_⟩
  change _ = (weylMap.line L).toAddSubgroup.toSubgroup.map e.toMonoidHom
  rw [hL, sourcePlane_image]

/-- Clauses 14.7.55(1)–(3) in the literal Weyl quotient. The line hypothesis
of the point-and-pencil theorem is constructed from the source local actions. -/
theorem weyl_source_point_and_pencil_of_local_actions
    (U V₁ V₂ V X T : Subgroup Q) [(V₁.subgroupOf U).Normal]
    (e : Multiplicative (TraceZero (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (hcardV : Nat.card ((V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 4)
    (hcardV₂ : Nat.card ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 2)
    (hV₂V : V₂ ≤ V) (hVU : V ≤ U) (hlocal : ⁅V, X⁆ ⊔ V₁ = V)
    (kX : X →* Model (ZMod 2)) (kT : T →* Model (ZMod 2))
    (hnXU : X ≤ normalizer (U : Set Q))
    (hnTU : T ≤ normalizer (U : Set Q)) (hnTV : T ≤ normalizer (V : Set Q))
    (hactX : ∀ (x : X) (v : U), traceZeroAction (ZMod 2) (kX x)
        ((sourceMap U V₁ e v).toAdd) =
      (sourceMap U V₁ e ⟨(x : Q) * v * (x : Q)⁻¹,
        le_normalizer_iff.mp hnXU x x.property v v.property⟩).toAdd)
    (hactT : ∀ (t : T) (v : U), traceZeroAction (ZMod 2) (kT t)
        ((sourceMap U V₁ e v).toAdd) =
      (sourceMap U V₁ e ⟨(t : Q) * v * (t : Q)⁻¹,
        le_normalizer_iff.mp hnTU t t.property v v.property⟩).toAdd)
    (S : Sylow 2 DerivedModel)
    (hS : (S : Subgroup DerivedModel).map DerivedModel.subtype ≤ kT.range) :
    ∃ L : ZeroProductLine (ZMod 2),
      (V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
        (weylQuotientGeometry (V₁.subgroupOf U) e).line L ∧
      (∃ p : SingularPoints (ZMod 2),
        (weylQuotientGeometry (V₁.subgroupOf U) e).point p =
          (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) ∧ pointOnLine p L) ∧
      Nat.card (quotientPencil (weylQuotientGeometry (V₁.subgroupOf U) e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) = 3 ∧
      Nat.card (quotientPencilSpan (weylQuotientGeometry (V₁.subgroupOf U) e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) = 8 := by
  obtain ⟨L, hL⟩ := weyl_source_line_of_local_actions U V₁ V X T e hcardV hVU hlocal
    kX kT hnXU hnTU hnTV hactX hactT S hS
  exact ⟨L, hL,
    CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.weyl_source_point_and_pencil
      U V₁ V₂ V e hcardV₂ hV₂V L hL⟩

end Applications

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
