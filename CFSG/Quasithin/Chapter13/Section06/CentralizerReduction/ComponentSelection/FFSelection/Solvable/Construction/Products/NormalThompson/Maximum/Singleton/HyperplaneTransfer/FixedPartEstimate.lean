module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer.FixedPartEstimate.NativeGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer.FixedPartEstimate.Linear

/-!
# The native hyperplane fixed-part estimate

Split off the selected S₃ moved plane. On its actual fixed complement, the
first SL₃(2) factor acts faithfully with three-dimensional moved space and
no fixed supplement. The natural marking and nonsplit extension estimate
give a bound for the rank of its elementary projection. The projection's
fixed codimension is exactly that of the ambient subgroup on this complement.

The final application supplies both codimension premises of the existing
maximum-transfer reduction. Its moved-plane dimension is the source support
order-four consequence supplied by the parent assembly. No rank, splitting,
cohomology or quotient-offender lifting hypothesis is added.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(5),
printed p.105, in the maximum construction of 13.6.13, printed p.929.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer

/-- The first native projection pays for its rank on the actual S₃ fixed
complement, including the nonsplit hyperplane extension. -/
theorem first_projection_rank_le_fixedPart_codim
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (c : HyperplaneCase ρ) (e : c.second ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (moved ρ c.second) = 2)
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) :
    rank (A.map c.product.fst) ≤ fixedCodim (fixedPart c).toRepresentation A := by
  rw [← FixedPartEstimate.first_projection_codim c A]
  exact FixedPartEstimate.nonsplit_rank_le_codim (FixedPartEstimate.firstAction c)
    (FixedPartEstimate.firstAction_faithful c hf e hd) c.firstEquiv
    (FixedPartEstimate.first_moved_dimension c hf e hd)
    (FixedPartEstimate.first_nonsplit c hf e hd) _ (hA.map c.product.fst)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open NormalThompson.Maximum.Singleton.HyperplaneTransfer

/-- The native hyperplane branch's actual maximum witness follows once the
selected support has its source moved-plane dimension. The selected S₃
marking and both codimension bounds are proved here. -/
theorem minimalSolvable_hyperplane_maximum_of_second_dimension
    {G : Type*} [Group G] [Finite G]
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (hd : Module.finrank (ZMod 2) (moved
      (FFFactors.offenderRepresentation (starRepresentation z v)) c.second) = 2) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      E.map (starMk z v) ≠ ⊥ := by
  obtain ⟨⟨e⟩, _⟩ := minimalSolvable_hyperplane_choice L T z v hz S hS hX c
  have hf := (starRepresentation_injective z v).comp
    (FFFactors.offenderActor (starRepresentation z v)).subtype_injective
  have hfixed := first_projection_rank_le_fixedPart_codim
    (FFFactors.offenderRepresentation (starRepresentation z v)) hf c e hd
  exact minimalSolvable_hyperplane_maximum_of_codimension_bounds
    L T z v hz S hS hfix hX c
    (fun A hA => projection_bound_of_fixedPart_bound _ hf c e hd A hA (hfixed A hA))
    hfixed

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
