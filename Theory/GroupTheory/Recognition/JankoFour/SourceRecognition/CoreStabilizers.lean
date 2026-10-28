module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCoreOrbits
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits.Counts
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Orders of the literal source quotient stabilizers

The full H/Q action has exactly the native label fibers as its vector orbits.
The certified singular fiber sizes, 693 and 1386, and orbit–stabilizer give
orders 3840 and 1920. The earlier central-coset adjustment identifies these
stabilizers with the images of the actual element centralizers under H → H/Q.
The final theorem supplies both distinct involution classes and these literal
centralizer-image orders, with no additional hypotheses.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.2), printed p.597, DOI 10.1007/BF01232280. The asserted
S₅/E₃₂ and S₅/E₁₆ structures are stronger than these orders and are not
claimed here. The later source fusion and geometry remain separate work.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup Sporadic.Mathieu Representation
variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
variable (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e))
variable [IsExtraspecial 2 (core z)]

omit [IsExtraspecial 2 (core z)] in
include h in
theorem coreQuotient_card : Nat.card (centralizer z ⧸ core z) = 2661120 := by
  obtain ⟨e⟩ := h.cubic_quotient
  have hA : Nat.card (MulAut M22) = 887040 := by
    exact (Nat.card_congr (MulEquiv.ofBijective m22DesignAutToAut
      ⟨m22DesignAutToAut_injective, m22DesignAutToAut_surjective⟩).toEquiv).symm.trans m22DesignAut_order
  have hc := e.projection.ker.card_mul_index
  rw [e.kernel_card, index_ker, MonoidHom.range_eq_top.mpr e.surjective, card_top, hA] at hc
  exact hc.symm

@[instance_reducible] private noncomputable def coreVectorAction :
    MulAction (centralizer z ⧸ core z) (CoreSpace (z := z)) where
  smul := fun g v => coreBinaryRepresentation h g v
  one_smul v := by change coreBinaryRepresentation h 1 v = v; rw [map_one]; rfl
  mul_smul a b v := by
    change coreBinaryRepresentation h (a*b) v =
      coreBinaryRepresentation h a (coreBinaryRepresentation h b v)
    rw [map_mul, Module.End.mul_apply]

theorem core_vector_orbit_iff_label (v w : CoreSpace (z := z)) :
    (∃ g : centralizer z ⧸ core z, coreBinaryRepresentation h g v = w) ↔
      VectorOrbits.label (coreNativeEquiv h e X v) =
        VectorOrbits.label (coreNativeEquiv h e X w) := by
  constructor
  · rintro ⟨g,rfl⟩
    exact (core_label_invariant h e X g v).symm
  · intro he
    obtain ⟨g,hg⟩ := (VectorOrbits.orbit_iff_label _ _).mpr he
    let c := (cubicCentralizerTripleEquiv h e X).symm g
    refine ⟨centerToCoreProjection h c.val, ?_⟩
    apply (coreNativeEquiv h e X).injective
    change coreNativeEquiv h e X (cubicCentralizerRepresentation h e X c v) = _
    rw [coreNativeEquiv_intertwines]
    simpa only [c, MulEquiv.apply_symm_apply] using hg

private theorem orbit_card (v : CoreSpace (z := z)) :
    letI := coreVectorAction h
    Nat.card (MulAction.orbit (centralizer z ⧸ core z) v) =
      Nat.card {w : M22TripleCover.BinarySpace //
        VectorOrbits.label w = VectorOrbits.label (coreNativeEquiv h e X v)} := by
  let := coreVectorAction h
  apply Nat.card_congr
  exact (coreNativeEquiv h e X).toEquiv.subtypeEquiv (fun w => by
    change (∃ g, coreBinaryRepresentation h g v = w) ↔ _
    rw [core_vector_orbit_iff_label h e X, eq_comm]
    rfl)

private theorem stabilizer_card_formula (r : core z) :
    Nat.card {w : M22TripleCover.BinarySpace //
      VectorOrbits.label w = VectorOrbits.label (coreNativeEquiv h e X
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)))} *
      Nat.card (coreVectorStabilizer h r) = 2661120 := by
  let := coreVectorAction h
  let v : CoreSpace (z := z) := Additive.ofMul (QuotientGroup.mk' (center (core z)) r)
  have hs : MulAction.stabilizer (centralizer z ⧸ core z) v = coreVectorStabilizer h r := by
    ext g
    rfl
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (centralizer z ⧸ core z) v)
  rw [Nat.card_prod, hs, coreQuotient_card h, orbit_card h e X v] at hc
  exact hc

/-- The first singular label has source quotient stabilizer of order 3840. -/
theorem coreVectorStabilizer_card_four (r : core z)
    (hr : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))) = 4) :
    Nat.card (coreVectorStabilizer h r) = 3840 := by
  have hc := stabilizer_card_formula h e X r
  rw [hr, VectorOrbits.label_four_card] at hc
  omega

/-- The second singular label has source quotient stabilizer of order 1920. -/
theorem coreVectorStabilizer_card_seven (r : core z)
    (hr : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))) = 7) :
    Nat.card (coreVectorStabilizer h r) = 1920 := by
  have hc := stabilizer_card_formula h e X r
  rw [hr, VectorOrbits.label_seven_card] at hc
  omega

omit [IsExtraspecial 2 (core z)] in
include h in
/-- Both distinct source classes and the orders of the actual images of
C_H(r) under H → H/Q. This does not yet assert their extension structures. -/
theorem source_involution_classes_stabilizers :
    ∃ r₁ r₂ : core z,
      orderOf r₁ = 2 ∧ orderOf r₂ = 2 ∧
      r₁ ∉ center (core z) ∧ r₂ ∉ center (core z) ∧
      ¬ IsConj (r₁ : centralizer z) (r₂ : centralizer z) ∧
      Nat.card ((Subgroup.centralizer ({(r₁ : centralizer z)} : Set (centralizer z))).map
        (QuotientGroup.mk' (core z))) = 3840 ∧
      Nat.card ((Subgroup.centralizer ({(r₂ : centralizer z)} : Set (centralizer z))).map
        (QuotientGroup.mk' (core z))) = 1920 ∧
      ∀ r : core z, orderOf r = 2 → r ∉ center (core z) →
        IsConj (r : centralizer z) (r₁ : centralizer z) ∨
          IsConj (r : centralizer z) (r₂ : centralizer z) := by
  let := h.extraspecial
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (LocalGeometry.CubicLift.subgroup e)))
  obtain ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,e₁,e₂,hcov⟩ := source_involution_orbit_cover h e X
  have hl₁ : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r₁))) = 4 := by
    rw [e₁,VectorOrbits.label_decode]
    rfl
  have hl₂ : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r₂))) = 7 := by
    rw [e₂,VectorOrbits.label_decode]
    rfl
  refine ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,?_,?_,?_,hcov⟩
  · intro hc
    have he := core_label_of_isConj h e X r₁ r₂ hc
    rw [hl₁,hl₂] at he
    exact (by decide : (4 : VectorOrbits.Word) ≠ 7) he
  · rw [← coreVectorStabilizer_eq_centralizer_image h r₁ h₁c]
    exact coreVectorStabilizer_card_four h e X r₁ hl₁
  · rw [← coreVectorStabilizer_eq_centralizer_image h r₂ h₂c]
    exact coreVectorStabilizer_card_seven h e X r₂ hl₂

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
