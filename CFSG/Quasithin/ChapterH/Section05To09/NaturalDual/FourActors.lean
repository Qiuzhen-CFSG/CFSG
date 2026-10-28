module

public import Theory.Representation.BinaryNaturalDual.FourActors
public import Theory.Representation.BinaryNaturalDual.FourActors.Parameters
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.FourActors.PermutationCatalogue
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.GeneratedCore

/-!
# The complete coordinate family H.9.3

For the actual automorphism group of the natural binary four-space, every
outer involution exchanges the natural and dual summands. The diagonal map
therefore gives the centralizer-equivariant fixed-module identification in
H.9.3(2), including equality with the actual displacement image.

`outer_involution_catalogue` and `elementary_sixteen_catalogue` give clauses
(1) and (3), including actual centralizer equivalences, conjugators and the
elementary Thompson identification. `outer_involution_fixed_module` gives
clause (2). The three numbered theorems below give clauses (4–6), both as
linear subspaces and through the actual E.3.30 generated-core convention.

The module calculations use the proved natural marking under the exceptional
comparison, the actual two-space radical identification, and the elementary
orders of the three representatives. Every additional premise of those
calculations is discharged. The imported `Parameters` module also retains
the three distinct transvection axes in B₂, the common fixed planes and the
mixed-sum/commutator identity from the proof on p.392.

The only input is the specified coordinate action on X ⊕ X*. Construction of
that action and comparison with an arbitrary source module belong to the H.9
source assembly; no source-module comparison is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3,
printed pp.391–392, PDF pp.402–403.
-/

public section

namespace CFSG.Quasithin.ChapterH.NaturalDual.FourActors
open BinaryNaturalDual BinaryNaturalDual.FourActors

/-- The coordinate form of H.9.3(2), retaining the actual diagonal map, its
inner-centralizer equivariance, and equality with the displacement image. -/
theorem outer_involution_fixed_module (d : CoordinateAction 4) (a : M)
    (ha : orderOf a = 2) (hout : a ∉ BinaryNaturalDual.FourActors.inner) :
    ∃ θ : X ≃ₗ[ZMod 2] fixedSpace (action d a),
      (∀ x : X, (θ x : V) = (x, 0) + d.representation a (x, 0)) ∧
      (∀ (g : G), a g = g → ∀ x : X,
        (θ (g x) : V) = d.representation (MulAut.conj g) (θ x : V)) ∧
      fixedSpace (action d a) = LinearMap.range (d.representation a - LinearMap.id) ∧
      Module.finrank (ZMod 2) (fixedSpace (action d a)) = 4 := by
  have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  exact ⟨outerDiagonalEquiv d a ha2 hout, outerDiagonalEquiv_apply d a ha2 hout,
    outerDiagonalEquiv_equivariant d a ha2 hout,
    outer_fixedSpace_eq_displacement d a ha2 hout, outer_fixedSpace_finrank d a ha2 hout⟩

/-- The coordinate actor core is exactly the subgroup core of E.3.30, with
the action restricted to the actual actor subgroup. -/
theorem actorCore_subgroup (d : CoordinateAction 4) (A : Subgroup M) (k : ℕ) :
    subgroupOrderIso (actorCore d A k) =
      ChapterE.dualGeneratedCore
        (multiplicativeAction
          (d.representation.comp A.subtype)) k :=
  generatedCore_subgroup (d.representation.comp A.subtype) k

/-- H.9.3(4), for the actual A₀ = J(T₁) from the three-class catalogue. -/
theorem lemma_H_9_3_4 (d : CoordinateAction 4) :
    Module.finrank (ZMod 2) (actorFixed d A0) = 4 ∧
    actorCore d A0 2 = ⊤ ∧
    ChapterE.dualGeneratedCore
      (multiplicativeAction
        (d.representation.comp A0.subtype)) 2 = ⊤ := by
  obtain ⟨hfix, hcore⟩ := Parameters.A0_parameters d
  refine ⟨hfix, hcore, ?_⟩
  rw [← actorCore_subgroup, hcore, OrderIso.map_top]

/-- H.9.3(5), retaining the actual unique natural transvection inducing r. -/
theorem lemma_H_9_3_5 (d : CoordinateAction 4) :
    r ∈ B1 ∧
    (∃ g : G, MulAut.conj g = r ∧ BinaryLinear.OuterCyclic.IsTransvection g ∧
      ∀ h : G, MulAut.conj h ∈ A1 → BinaryLinear.OuterCyclic.IsTransvection h → h = g) ∧
    Module.finrank (ZMod 2) (actorFixed d A1) = 1 ∧
    actorCore d A1 2 = BinaryNaturalDual.fixedSpace (action d r) ∧
    Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace (action d r)) = 6 ∧
    ChapterE.dualGeneratedCore
      (multiplicativeAction
        (d.representation.comp A1.subtype)) 2 =
      subgroupOrderIso
        (BinaryNaturalDual.fixedSpace (action d r)) := by
  obtain ⟨hfix, hcore, hdim⟩ := Parameters.A1_parameters d
  refine ⟨r_mem_B1, Parameters.A1_transvection, hfix, hcore, hdim, ?_⟩
  rw [← actorCore_subgroup, hcore]

/-- H.9.3(6), for every outer element of the mixed representative. The final
equality uses the subgroup join corresponding to the source's sum of modules. -/
theorem lemma_H_9_3_6 (d : CoordinateAction 4) {a : M} (ha : a ∈ A2) (haB : a ∉ B2) :
    (∀ v : V, v ∈ actorFixed d A2 ↔ ∃ x ∈ naturalFixed B2,
      (x, 0) + d.representation a (x, 0) = v) ∧
    Module.finrank (ZMod 2) (actorFixed d A2) = 2 ∧
    actorCore d A2 2 = actorFixed d B2 ⊔ BinaryNaturalDual.fixedSpace (action d a) ∧
    Module.finrank (ZMod 2)
      ↥(actorFixed d B2 ⊔ BinaryNaturalDual.fixedSpace (action d a)) = 6 ∧
    ChapterE.dualGeneratedCore
      (multiplicativeAction
        (d.representation.comp A2.subtype)) 2 =
      subgroupOrderIso (actorFixed d B2) ⊔
        subgroupOrderIso
          (BinaryNaturalDual.fixedSpace (action d a)) := by
  obtain ⟨hdiag, hfix, hcore, hdim⟩ := Parameters.A2_parameters d ha haB
  refine ⟨hdiag, hfix, hcore, ?_, ?_⟩
  · rwa [← hcore]
  · rw [← actorCore_subgroup, hcore, OrderIso.map_sup]

end CFSG.Quasithin.ChapterH.NaturalDual.FourActors
