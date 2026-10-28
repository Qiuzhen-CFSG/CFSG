module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer.Reduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer.FixedPartEstimate
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Transport

/-!
# The native hyperplane singleton maximum witness

The source selection supplies the actual S₃ marking and ambient normality.
The support order four supplies the moved-plane dimension under the literal
star action. The native SL₃(2) estimate on the complementary fixed part
then gives a maximum elementary subgroup of the full selected preimage
whose star image is nontrivial.

The moved-space decomposition and hyperplane clause supply the nonsplit
fixed-part estimate; no module splitting or quotient-offender lifting
premise remains. The only support input is its order four, supplied by
the separate support construction in the final 13.6.13 assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(5), printed p.105, and 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
variable {G : Type*} [Group G] [Finite G]
open NormalThompson.Maximum.Singleton.HyperplaneTransfer

private theorem hyperplane_second_dimension (z v : G)
    [IsElementaryAbelian 2 (Uv z v)]
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (hcard : Nat.card (movedSubgroup z v
      (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype)) = 4) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.ChapterB.QuasisimpleSource.moved
      (FFFactors.offenderRepresentation (starRepresentation z v)) c.second) = 2 := by
  let I := FFFactors.offenderActor (starRepresentation z v)
  have hm : subspaceCommutator (FFFactors.offenderRepresentation (starRepresentation z v)) ⊤ c.second =
      subspaceCommutator (starRepresentation z v) ⊤ (c.second.map I.subtype) := by
    unfold subspaceCommutator
    congr 1
    ext w
    constructor
    · rintro ⟨a, ha, u, hu, rfl⟩
      exact ⟨I.subtype a, mem_map_of_mem _ ha, u, hu, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, u, hu, rfl⟩
      exact ⟨a, ha, u, hu, rfl⟩
  have hc : Nat.card (subspaceCommutator
      (FFFactors.offenderRepresentation (starRepresentation z v)) ⊤ c.second) = 4 := by
    rw [hm, ← ambientSpace_card, moved_ambientSpace]
    exact hcard
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hc

/-- Conditional assembly from a fixed-part projection bound. The native
estimate discharges this premise in `minimalSolvable_hyperplane_maximum_of_support`. -/
theorem minimalSolvable_hyperplane_maximum_of_fixedPart_bound
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (hcard : Nat.card (movedSubgroup z v
      (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype)) = 4)
    (hfixed : ∀ A : Subgroup (FFFactors.offenderActor (starRepresentation z v)),
      IsElementaryAbelian 2 A →
      rank (A.map c.product.fst) ≤ fixedCodim (fixedPart c).toRepresentation A) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      E.map (starMk z v) ≠ ⊥ := by
  obtain ⟨⟨e⟩, _⟩ := minimalSolvable_hyperplane_choice L T z v hz S hS hX c
  apply minimalSolvable_hyperplane_maximum_of_codimension_bounds
    L T z v hz S hS hfix hX c _ hfixed
  intro A hA
  exact projection_bound_of_fixedPart_bound
    (FFFactors.offenderRepresentation (starRepresentation z v))
    ((starRepresentation_injective z v).comp
      (FFFactors.offenderActor (starRepresentation z v)).subtype_injective)
    c e (hyperplane_second_dimension z v c hcard) A hA (hfixed A hA)

/-- The native hyperplane branch has a moving maximum elementary subgroup
in the full selected preimage. Support order four supplies the moved-plane
dimension; the native fixed-part estimate supplies both rank comparisons. -/
theorem minimalSolvable_hyperplane_maximum_of_support
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (hcard : Nat.card (movedSubgroup z v
      (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype)) = 4) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      E.map (starMk z v) ≠ ⊥ := by
  exact minimalSolvable_hyperplane_maximum_of_second_dimension
    L T z v hz S hS hfix hX c (hyperplane_second_dimension z v c hcard)

/-- The same witness on the actual marked A₅ configuration, with the original
star quotient and the full preimage. Its order-four support input is retained
for the support producer in the final source assembly. -/
theorem marked_minimalSolvable_hyperplane_maximum_of_support
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)))) :
    let z := A5Module.markedZ s
    let v := A5Module.markedV s
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
    ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      E.map (starMk z v) ≠ ⊥ := by
  exact minimalSolvable_hyperplane_maximum_of_support L T _ _
    (A5Module.markedZ_mem_Gv s) S hS hfix hX c

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
