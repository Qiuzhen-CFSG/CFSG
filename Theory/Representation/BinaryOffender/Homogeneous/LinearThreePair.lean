module
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreeInertia
public import Theory.Representation.BinaryOffender.IrreducibleOrbitGeometry

/-!
# A moved pair of natural binary-three central covers

A homogeneous seed has at most two conjugates under a component normalizer.
If it is moved, the two central images are disjoint and each has dimension
three. Their span therefore has dimension six modulo the component-fixed
space. The original orbit has dimension six, seven, or eight: the possible
central covering lines are retained throughout.

The literal terminal support application is in Chapter14/Section06/
SourceSuitableChoice/ComponentSupports/Modules/Recognition/LinearThreeMovement.
Source: Aschbacher--Smith A.1.40--42 and 14.6.22, pp.31--32 and1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K T : Subgroup D}
    {I : Submodule (ZMod 2) V}

/-- A moved homogeneous natural-cover seed has exactly two disjoint central
images, whose sum has dimension six; the full orbit retains its central kernel. -/
theorem IsIrrPlusWith.linear_three_moved_pair
    (hI : IsIrrPlusWith ρ K T I)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v))
    (hmoved : orbitSpan ρ T I ≠ I) :
    ∃ t : T, I.map (ρ t.val) ≠ I ∧
      orbitSpan ρ T I = I ⊔ I.map (ρ t.val) ∧
      Disjoint (I.map (fixedSpace ρ K).mkQ) ((I.map (ρ t.val)).map (fixedSpace ρ K).mkQ) ∧
      Module.finrank (ZMod 2) ((orbitSpan ρ T I).map (fixedSpace ρ K).mkQ) = 6 ∧
      (Module.finrank (ZMod 2) (orbitSpan ρ T I) = 6 ∨
       Module.finrank (ZMod 2) (orbitSpan ρ T I) = 7 ∨
       Module.finrank (ZMod 2) (orbitSpan ρ T I) = 8) := by
  obtain ⟨t,ht⟩ := hI.linear_three_orbit_span ρ j
  have hne : I.map (ρ t.val) ≠ I := by
    intro hh
    exact hmoved (ht.trans (by rw [hh,sup_idem]))
  have hj := hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)
  have hd := hI.isIrrPlus.disjoint_quotientImages ρ hj (Ne.symm hne)
  have hr : Module.finrank (ZMod 2) (I.map (fixedSpace ρ K).mkQ) = 3 := by
    rw [←(centralQuotientImageEquiv ρ K I).finrank_eq,l.finrank_eq]
    exact Module.finrank_fin_fun (ZMod 2)
  have hdim : Module.finrank (ZMod 2) ((orbitSpan ρ T I).map (fixedSpace ρ K).mkQ) = 6 := by
    have hh := (I.map (fixedSpace ρ K).mkQ).finrank_sup_add_finrank_inf_eq
      ((I.map (ρ t.val)).map (fixedSpace ρ K).mkQ)
    rw [hd.eq_bot,finrank_bot,add_zero,finrank_quotientOrbit ρ K I (hI.normalizes t.property),hr] at hh
    rw [ht,Submodule.map_sup]
    exact hh
  have hu := hI.linear_three_orbit_finrank_le ρ j
  have hi := hI.isIrrPlus.finrank_of_linear_three_central_quotient ρ K j l he
  have hl := Submodule.finrank_map_le (fixedSpace ρ K).mkQ (orbitSpan ρ T I)
  exact ⟨t,hne,ht,hd,hdim,by omega⟩

end Representation.BinaryOffender.Homogeneous
