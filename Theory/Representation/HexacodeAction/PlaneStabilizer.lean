module

public import Theory.Representation.HexacodeAction.PlaneStabilizer.Action
public import Theory.AtlasPort.OtherSporadic.Families.Alternating.Stabilizers

/-!
# The A₅ quotient of a full-weight hexacode plane stabilizer

The even hexacode group acts onto the alternating group on its six
full-weight scalar planes. For any one of these actual binary subspaces,
restriction gives a surjection from its even setwise stabilizer to the
point stabilizer in that alternating group. Restriction to the other five
planes identifies the latter group with `alternatingGroup (Fin 5)`.

The source is the final contradiction in the proof of 15.3.1 on printed
p.1155 (PDF p.1172) of Aschbacher–Smith, *The Classification of Quasithin
Groups* (combined manuscript, 1 March 2004). This module proves the concrete
model calculation. Recognition of the source action and transport of its
specified plane are separate obligations of the source-theorem assembly.
The underlying hexacode and the alternating stabilizer equivalence are
existing ATLAS ports, attributed in their owning modules.
-/

public section

open Atlas.Codes
namespace Representation.Hexacode

private noncomputable def planeStabilizerToFixing
    (P : Submodule (ZMod 2) hexacode) (hP : IsFullWeightScalarPlane P) :
    (hexSign.ker ⊓ BinaryOffender.subspaceStabilizer action P : Subgroup HexAutomorphisms) →*
      fixingSubgroup (alternatingGroup FullWeightScalarPlane)
        (({⟨P,hP⟩} : Finset FullWeightScalarPlane) : Set FullWeightScalarPlane) :=
  (planeAlternating.comp (Subgroup.inclusion inf_le_left)).codRestrict _ (by
    rintro g ⟨Q,hQ⟩
    have he : Q = ⟨P,hP⟩ := Finset.mem_singleton.mp hQ
    subst Q
    exact (planePerm_fixed_iff ⟨g.val,g.property.1⟩ ⟨P,hP⟩).2 g.property.2)

private theorem planeStabilizerToFixing_surjective
    (P : Submodule (ZMod 2) hexacode) (hP : IsFullWeightScalarPlane P) :
    Function.Surjective (planeStabilizerToFixing P hP) := by
  intro k
  obtain ⟨g,hg⟩ := planeAlternating_surjective k.val
  have hfix : planePerm g ⟨P,hP⟩ = ⟨P,hP⟩ := by
    change (planeAlternating g).val ⟨P,hP⟩ = ⟨P,hP⟩
    rw [hg]
    exact k.property ⟨⟨P,hP⟩, Finset.mem_singleton_self _⟩
  refine ⟨⟨g.val, g.property, (planePerm_fixed_iff g ⟨P,hP⟩).1 hfix⟩, ?_⟩
  exact Subtype.ext hg

private noncomputable def planeFixingA5Equiv (P : FullWeightScalarPlane) :
    fixingSubgroup (alternatingGroup FullWeightScalarPlane)
        (({P} : Finset FullWeightScalarPlane) : Set FullWeightScalarPlane) ≃*
      alternatingGroup (Fin 5) := by
  classical
  refine (Atlas.Families.Alternating.stabilizerComplementEquiv {P}).trans
    (Atlas.Families.Alternating.relabel (Fintype.equivFinOfCardEq ?_))
  simp [fullWeightScalarPlane_card]

/-- The concrete A₅ quotient of the even stabilizer of any full-weight scalar plane. -/
noncomputable def fullWeightScalarPlaneStabilizerA5
    (P : Submodule (ZMod 2) hexacode) (hP : IsFullWeightScalarPlane P) :
    (hexSign.ker ⊓ BinaryOffender.subspaceStabilizer action P : Subgroup HexAutomorphisms) →*
      alternatingGroup (Fin 5) :=
  (planeFixingA5Equiv ⟨P,hP⟩).toMonoidHom.comp (planeStabilizerToFixing P hP)

/-- Restriction of the six-plane action onto the five remaining planes is surjective. -/
theorem fullWeightScalarPlaneStabilizerA5_surjective
    (P : Submodule (ZMod 2) hexacode) (hP : IsFullWeightScalarPlane P) :
    Function.Surjective (fullWeightScalarPlaneStabilizerA5 P hP) :=
  (planeFixingA5Equiv ⟨P,hP⟩).surjective.comp (planeStabilizerToFixing_surjective P hP)

/-- Existential interface for transporting this calculation to an isomorphic action. -/
theorem exists_surjective_planeStabilizer_A5
    (P : Submodule (ZMod 2) hexacode) (hP : IsFullWeightScalarPlane P) :
    ∃ f : (hexSign.ker ⊓ BinaryOffender.subspaceStabilizer action P : Subgroup HexAutomorphisms) →*
        alternatingGroup (Fin 5), Function.Surjective f :=
  ⟨fullWeightScalarPlaneStabilizerA5 P hP, fullWeightScalarPlaneStabilizerA5_surjective P hP⟩

end Representation.Hexacode
