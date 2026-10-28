module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Inputs
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy
public import Theory.AlgebraicGroup.Jordan.FiniteOrder

/-!
# Binary Ree torus placement after Borel element coverage

An element of order five or thirteen is semisimple after the actual coefficient
embedding in characteristic two. Inside a Borel, the connected normal unipotent
radical conjugates a semisimple point into a torus complement. Map that torus
into the ambient F4 carrier, extend it to a maximal torus, and use the checked
maximal-torus conjugacy theorem. The coordinate bridge then gives the literal
positive-coroot product, with its inverse diagonal-parameter convention.

`placement_of_borel_coverage` supplies every step of the requested placement
except the connected-group Borel element-coverage theorem. It discharges the
actual F4 carrier's connectedness; the remaining source clause is an explicit
input. This is a conditional reduction, not unconditional `Placement F`.
The existing `BorelElementCoverage` development owns that geometric input.
No connectedness of a finite cyclic Zariski closure is used.

Sources: GLS3, Propositions 1.2.2(e), 1.4.2(e), Theorem 1.6.3;
Borel, *Linear Algebraic Groups*, Theorems 10.6(4) and 11.10.
The binary Ree application is the torus-placement step for Guralnick--Malle II,
Lemma 8.8 (internal p.57). Its consumer is
`TorusCoverage.coverage_of_placement_balance_spectrum`.
-/

public section

open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage

variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

omit [CharP F 2] in
private theorem borel_carrier_connected
    (B : ClosedSubgroup (F4Chevalley.Carrier (k := F))) (hB : IsBorelSubgroup B) :
    Variety.IsConnected B.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point (F4Chevalley.Carrier (k := F)) //
      x ∈ (B : Set (Variety.Point (F4Chevalley.Carrier (k := F))))} :=
    Subtype.connectedSpace hB.connected
  let : ConnectedSpace (Variety.Point B.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- Semisimple containment in a Borel gives an actual conjugator and positive
coroot coordinates. The radical's normality is used only in the Borel carrier. -/
theorem exists_coroot_conjugate_of_mem_borel
    (B : ClosedSubgroup (F4Chevalley.Carrier (k := F))) (hB : IsBorelSubgroup B)
    (s : Variety.Point (F4Chevalley.Carrier (k := F)))
    (hs : IsSemisimpleElement (F4Chevalley.Carrier (k := F)) s)
    (hsB : s ∈ B.toSubgroup) :
    ∃ (c : Variety.Point (F4Chevalley.Carrier (k := F))) (t : Fin 4 → Fˣ),
      s = c * corootTorusElement t * c⁻¹ := by
  let := B.carrierAlgebraicGroup
  have hconn := borel_carrier_connected B hB
  obtain ⟨U, hUrad, hUconn, T, hT, _⟩ :=
    exists_maximalTorus_complement_of_solvable_connected hB.solvable hconn
  let sB := B.pointEquiv.symm ⟨s, hsB⟩
  have hsBval : B.inclusion.onPoints sB = s :=
    congrArg Subtype.val (B.pointEquiv.apply_symm_apply _)
  have hsSemi : IsSemisimpleElement B.carrierVariety sB :=
    (closedSubgroup_semisimpleElement_iff B hsB).mp hs
  obtain ⟨u, _, huT⟩ :=
    semisimpleElement_conjugate_into_subtorus_of_unipotent_factorization
      T U hT.1 hUconn
      (hUrad.isUnipotent_of_solvable_connected hB.solvable hconn)
      (hUrad.normal_of_solvable_connected hB.solvable hconn) hT.2.1 sB hsSemi
  let := T.carrierAlgebraicGroup
  let j := B.inclusion.comp T.inclusion
  have hS : IsSubtorus j.imageClosedSubgroup := morphism_image_isTorus j hT.1
  obtain ⟨M, hM, hSM⟩ := exists_maximalTorus_containing j.imageClosedSubgroup hS
  have huM : (B.inclusion.onPoints u)⁻¹ * s * B.inclusion.onPoints u ∈ M := by
    apply hSM
    refine ⟨T.pointEquiv.symm ⟨u⁻¹ * sB * u, huT⟩, ?_⟩
    change B.inclusion.onPoints
      ((T.pointEquiv (T.pointEquiv.symm ⟨u⁻¹ * sB * u, huT⟩)).val) = _
    rw [T.pointEquiv.apply_symm_apply]
    simp only [map_mul, map_inv, hsBval]
  obtain ⟨a, ha⟩ := F4Chevalley.TorusConjugacy.maximalTori_conjugate
    (F4Chevalley.splitTorus (k := F)) M
    F4Chevalley.TorusConjugacy.splitTorus_isMaximal hM
  rw [ha, ClosedSubgroup.mem_conjugate_iff] at huM
  obtain ⟨t, ht⟩ := (mem_splitTorus_iff _).mp huM
  refine ⟨B.inclusion.onPoints u * a, t, ?_⟩
  rw [ht]
  group

/-- Both relevant odd orders give semisimplicity in the literal ambient carrier,
using the power equation transported through the actual embedding. -/
theorem binaryOdd_splitEmbedding_semisimple
    (f : CoefficientField 0 →+* F) (x : Model 0)
    (hx : orderOf x = 5 ∨ orderOf x = 13) :
    IsSemisimpleElement (F4Chevalley.Carrier (k := F))
      (Classification.splitEmbedding f (toSplitGroup 0 x)) := by
  apply finiteOrder_coprimeChar_implies_semisimple _ (orderOf x)
  · omega
  · rw [ringChar.eq F 2]
    rcases hx with hx | hx <;> simp [hx]
  · change (((Classification.splitEmbedding f).comp (toSplitGroup 0)) x) ^ _ = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]

/-- Apply connected-group Borel coverage to the concrete connected F4 carrier.
The only remaining input is the source element-coverage clause; torus placement,
conjugacy, coroot coordinates, and finite-order semisimplicity are proved here. -/
theorem placement_of_borel_coverage
    (hcoverage : Variety.IsConnected (F4Chevalley.Carrier (k := F)) →
      ∀ B : ClosedSubgroup (F4Chevalley.Carrier (k := F)),
      IsBorelSubgroup B → ∀ s : Variety.Point (F4Chevalley.Carrier (k := F)),
        ∃ b : Variety.Point (F4Chevalley.Carrier (k := F)),
          b⁻¹ * s * b ∈ B.toSubgroup) : Placement F := by
  intro f x hx
  obtain ⟨B, hB⟩ := exists_borelSubgroup (F4Chevalley.Carrier (k := F))
  obtain ⟨b, hb⟩ := hcoverage F4Chevalley.carrier_isConnected B hB
    (Classification.splitEmbedding f (toSplitGroup 0 x))
  apply exists_coroot_conjugate_of_mem_borel (B.conjugate b) (hB.conjugate b)
    _ (binaryOdd_splitEmbedding_semisimple f x hx)
  exact (B.mem_conjugate_iff b _).mpr hb

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage
