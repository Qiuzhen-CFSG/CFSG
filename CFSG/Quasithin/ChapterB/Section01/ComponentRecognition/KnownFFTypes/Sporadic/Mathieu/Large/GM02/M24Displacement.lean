module
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Placement.Source

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.GM02.Reduction
public import Theory.Representation.Mathieu.M24Degree44Displacement

/-!
# GM02's M₂₄ displacement reduction to the order-five calculation

The native involution geometry, commutator rank inequality, and transport
through every allowed quasisimple cover are proved in Theory. The order-five
fixed-space calculation supplies the published displacement contract and
excludes degree 44 for the actual source action, independently of the
generation and low-degree spectrum inputs.

The displacement contract is unconditional; the earlier conditional APIs remain available.
Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, author manuscript p.17.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Sporadic.Mathieu
open Representation.MathieuM24Degree44
universe u v

/-- The precise native order-five calculation supplies the cover-preserving GM02 contract. -/
theorem m24Degree44Displacement_of_fiveFixedSpaceBound (hfive : FiveFixedSpaceBound.{v}) :
    M24Degree44Displacement.{u,v} := by
  intro L _ _ _ V _ _ _ ρ hf hi he hd t ht ht2
  obtain ⟨e⟩ := he
  exact cover_displacement_of_fiveFixedSpaceBound hfive ρ hf hi e hd t ht ht2

/-- Actual source application: the order-five calculation excludes the degree-44 row. -/
theorem m24_degree_ne_forty_four_of_fiveFixedSpaceBound (hfive : FiveFixedSpaceBound.{v})
    {G : Type u} [Group G] [Finite G] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M24) :
    Module.finrank (ZMod 2) V ≠ 44 :=
  m24_degree_ne_forty_four (m24Degree44Displacement_of_fiveFixedSpaceBound hfive) ρ h e

/-- The complete native placement and exterior calculation discharge the
cover-preserving displacement contract. -/
theorem m24Degree44Displacement : M24Degree44Displacement.{u,v} :=
  m24Degree44Displacement_of_fiveFixedSpaceBound fiveFixedSpaceBound

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
