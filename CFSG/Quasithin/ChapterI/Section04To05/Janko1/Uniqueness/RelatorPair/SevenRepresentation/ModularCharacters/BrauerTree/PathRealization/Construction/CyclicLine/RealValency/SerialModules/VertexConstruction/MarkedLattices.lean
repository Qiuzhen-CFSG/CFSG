module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.VertexConstruction.Contracts
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.VertexConstruction.MarkedLattices

/-!
# Marked lattices at the actual principal eleven-block prime

Every ordinary lattice reduces with the incident-edge Brauer character, for
the precise localization and residue map in the source input. This follows
from the integral characteristic-polynomial comparison and the regular-order
bound 15960, without any projective lifting assumption.

The conditional assembly below combines two remaining source obligations:
the composition-factor identification and the choice of a lattice with a
prescribed simple socle. They must both be supplied before claiming existence
of VertexFlags. Source: Feit I.17.12, IV.2.1(vi), and the lattices X_ui on p.279.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation.CyclicDefect.PrimeOrderRealLine
open RealValency.SerialModules

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- The unconditional regular-character identity for each literal ordinary
lattice reduction. This is the input to composition-factor identification. -/
public theorem principalBlock_lattice_reduction_value
    (b : PrincipalBlockIdentification d) (horder : Nat.card G = 175560)
    (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (v : {i // i ∈ b.data.block}) (X : OrdinaryLattice b.data v.val)
    (g : G) (hg : ¬ 11 ∣ orderOf g) :
    (principalBlock_rootLift b r).value (X.reduction r) g =
      ∑ e ∈ t.incident v, (principalBlock_rootLift b r).value (t.rep e) g := by
  let : NeZero (15960 : ElevenClosure) := ⟨by
    exact (CharP.cast_eq_zero_iff ElevenClosure 11 15960).not.mpr (by decide)⟩
  exact reduction_value_eq_incident_sum r t v X g hg
    (regular_order_dvd_root_order horder g hg)

/-- At every group element, the reduced trace is the sum of the incident
simple traces. The natural degree identity remains available separately,
so later multiplicity arguments need not infer integers from residues alone. -/
public theorem principalBlock_lattice_reduction_character
    (b : PrincipalBlockIdentification d) (horder : Nat.card G = 175560)
    (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (v : {i // i ∈ b.data.block}) (X : OrdinaryLattice b.data v.val) (g : G) :
    (X.reduction r).character g = ∑ e ∈ t.incident v, (t.rep e).character g := by
  let : NeZero (15960 : ElevenClosure) := ⟨by
    exact (CharP.cast_eq_zero_iff ElevenClosure 11 15960).not.mpr (by decide)⟩
  exact reduction_character_eq_incident_sum r t
    (regular_order_dvd_root_order horder) v X g

/-- Final family assembly once both independent source constructions have
been proved. An arbitrary ordinary lattice discharges the initial occurrence
premise of selection; the selected lattices then receive their own flags. -/
public theorem principalBlock_vertexFlags_exists_of_selection
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (flags : ∀ (v : {i // i ∈ b.data.block}) (X : OrdinaryLattice b.data v.val),
      Nonempty (IncidentFlag t r v X))
    (select : ∀ (v : {i // i ∈ b.data.block}) (X : OrdinaryLattice b.data v.val),
      IncidentFlag t r v X → ∀ e : ↥(t.incident v), Nonempty (MarkedLattice t r v e)) :
    Nonempty (∀ v : {i // i ∈ b.data.block}, VertexFlags t r v) :=
  exists_vertexFlags_of_selection t r flags select

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
