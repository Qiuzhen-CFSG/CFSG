module

public import Theory.AlgebraicGroup.Borel.RootBorelDecomposition

universe u

/-!
This module is the witness boundary for the actual-root-generation argument.
For a selected positive system, `CompatibleBorelWitnesses` keeps the positive
and opposite Borel subgroups together with the full radical and torus-factor
data stored in `IsBorelOfPositiveSystem`.  The conversion to
`RealizedRootBorelOppositeData` is therefore projection-only and uses no
numbered theorem.

The existence fields in this module are deliberately explicit.  Constructing
the two geometric Borel/root witnesses is the content of GLS3 Theorem 1.11.2;
the unresolved numbered transcription is not used as an assumption here.  A
caller that has supplied those source witnesses can immediately obtain the
reusable opposite-data package and its pointwise decompositions.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

section

variable {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T}
    {P : Set D.Root}

/-- A positive system together with compatible positive and opposite Borel
root witnesses.  Each witness contains its Borel subtype, unipotent radical,
radical maximality, root-generation equality, and torus factorization. -/
public structure CompatibleBorelWitnesses where
  positive_system : IsPositiveSystem D P
  B : ClosedSubgroup K
  Bopp : ClosedSubgroup K
  positive_witness : IsBorelOfPositiveSystem D P B
  opposite_witness : IsBorelOfPositiveSystem D (D.neg ⁻¹' P) Bopp

/-- A Borel/root witness determines the corresponding torus-containing Borel.
The containment is obtained from its stored torus-radical factorization. -/
public def IsBorelOfPositiveSystem.toBorelContaining
    {B : ClosedSubgroup K} (hB : IsBorelOfPositiveSystem D P B) :
    BorelContaining T where
  carrier := B
  isBorel := hB.borel
  torus_le := by
    intro x hx
    change x ∈ B.toSubgroup
    rw [hB.torus_unipotent_generate]
    exact Subgroup.mem_sup_left hx

/-- The positive Borel as an explicit torus-containing subtype. -/
public def CompatibleBorelWitnesses.positive_borelContaining
    (H : CompatibleBorelWitnesses (T := T) (D := D) (P := P)) :
    BorelContaining T := H.positive_witness.toBorelContaining

/-- The opposite Borel as an explicit torus-containing subtype. -/
public def CompatibleBorelWitnesses.opposite_borelContaining
    (H : CompatibleBorelWitnesses (T := T) (D := D) (P := P)) :
    BorelContaining T := H.opposite_witness.toBorelContaining

/-- Package separately supplied positive and opposite witnesses. -/
public def CompatibleBorelWitnesses.of_witnesses
    (hP : IsPositiveSystem D P)
    {B Bopp : ClosedSubgroup K}
    (hB : IsBorelOfPositiveSystem D P B)
    (hBopp : IsBorelOfPositiveSystem D (D.neg ⁻¹' P) Bopp) :
    CompatibleBorelWitnesses (T := T) (D := D) (P := P) :=
  { positive_system := hP
    B := B
    Bopp := Bopp
    positive_witness := hB
    opposite_witness := hBopp }

/-- Convert the explicit witness structure to the common package consumed by
the opposite-Borel and root-generation interfaces. -/
public def CompatibleBorelWitnesses.toRealized
    (H : CompatibleBorelWitnesses (T := T) (D := D) (P := P)) :
    RealizedRootBorelOppositeData T D P :=
  RealizedRootBorelOppositeData.of_witnesses H.positive_system
    H.positive_witness H.opposite_witness

/-- Existential witness form, retaining the Borel-containing subtypes. -/
public theorem exists_compatibleBorelWitnesses
    (hP : IsPositiveSystem D P)
    (hB : ∃ B : ClosedSubgroup K,
      Nonempty (IsBorelOfPositiveSystem D P B))
    (hBopp : ∃ Bopp : ClosedSubgroup K,
      Nonempty (IsBorelOfPositiveSystem D (D.neg ⁻¹' P) Bopp)) :
    Nonempty (CompatibleBorelWitnesses (T := T) (D := D) (P := P)) := by
  obtain ⟨B, ⟨hB⟩⟩ := hB
  obtain ⟨Bopp, ⟨hBopp⟩⟩ := hBopp
  exact ⟨CompatibleBorelWitnesses.of_witnesses hP hB hBopp⟩

/-- The same existential data with the Borel subtypes made explicit. -/
public theorem exists_compatibleBorelContaining_witnesses
    (_hP : IsPositiveSystem D P)
    (hB : ∃ B : ClosedSubgroup K,
      Nonempty (IsBorelOfPositiveSystem D P B))
    (hBopp : ∃ Bopp : ClosedSubgroup K,
      Nonempty (IsBorelOfPositiveSystem D (D.neg ⁻¹' P) Bopp)) :
    ∃ B Bopp : BorelContaining T,
      Nonempty (IsBorelOfPositiveSystem D P B.carrier) ∧
      Nonempty (IsBorelOfPositiveSystem D (D.neg ⁻¹' P) Bopp.carrier) := by
  obtain ⟨B, ⟨hB⟩⟩ := hB
  obtain ⟨Bopp, ⟨hBopp⟩⟩ := hBopp
  refine ⟨hB.toBorelContaining, hBopp.toBorelContaining, ?_, ?_⟩
  · exact ⟨hB⟩
  · exact ⟨hBopp⟩

/-- Existential positive/opposite Borel witnesses feed directly into
`RealizedRootBorelOppositeData.exists_of_witnesses`. -/
public theorem exists_realizedRootBorelOppositeData_of_witnesses
    (hP : IsPositiveSystem D P)
    (hB : ∃ B : ClosedSubgroup K,
      Nonempty (IsBorelOfPositiveSystem D P B))
    (hBopp : ∃ Bopp : ClosedSubgroup K,
      Nonempty (IsBorelOfPositiveSystem D (D.neg ⁻¹' P) Bopp)) :
    Nonempty (RealizedRootBorelOppositeData T D P) :=
  RealizedRootBorelOppositeData.exists_of_witnesses hP hB hBopp

/-- The subtype-preserving form of the previous constructor. -/
public theorem exists_realizedRootBorelOppositeData_of_borelContaining_witnesses
    (hP : IsPositiveSystem D P)
    (hB : ∃ B : BorelContaining T,
      Nonempty (IsBorelOfPositiveSystem D P B.carrier))
    (hBopp : ∃ Bopp : BorelContaining T,
      Nonempty (IsBorelOfPositiveSystem D (D.neg ⁻¹' P) Bopp.carrier)) :
    Nonempty (RealizedRootBorelOppositeData T D P) := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨Bopp, hBopp⟩ := hBopp
  exact RealizedRootBorelOppositeData.exists_of_witnesses hP
    ⟨B.carrier, hB⟩ ⟨Bopp.carrier, hBopp⟩

end

end Theory.AlgebraicGroup
