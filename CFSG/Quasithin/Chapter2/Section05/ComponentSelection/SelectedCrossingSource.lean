module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SquareMovingSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingDerivedSource
/-! # A displaced derived subgroup selected from the original source setup
The proved plane and square-moving choice discharges both witness premises
of the derived-core placement. Every surviving rank-two model now supplies
an actual outside crossing actor, with its nontrivial displaced derived
subgroup lying in J(S)∩O₂(H) and normalized by the original S.
Source: Aschbacher--Smith 2.5.7, printed p.556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}

theorem MathieuSourceSetup.linear_simple_selected_crossing_derived_core
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F)) :
    let Y:=(S:Subgroup H).map H.subtype
    let D:=⁅Y⊓L,Y⊓L⁆
    ∃x:G,x∈c.T ∧ x∉Y ∧ x∈normalizer (Y:Set G) ∧ x^2∈Y ∧
      D.conjBy x⁻¹≠⊥ ∧ D.conjBy x⁻¹≤elementaryAbelianMaxJ Y⊓twoCore H ∧
      Y≤normalizer (D.conjBy x⁻¹:Set G) := by
  obtain ⟨V,hV,x,hxT,hxS,hxN,hx2,hm⟩:=
    MathieuSourceSetup.linear_simple_square_moving_plane c hG hempty hgen F hn hF e
  exact ⟨x,hxT,hxS,hxN,hx2,
    MathieuSourceSetup.linear_simple_crossing_derived_core c hG hempty hgen F hn hF e
      V hV x hxT hxS hxN hx2 hm⟩

theorem MathieuSourceSetup.linear_four_selected_crossing_derived_core
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL) :
    let Y:=(S:Subgroup H).map H.subtype
    let D:=⁅Y⊓L,Y⊓L⁆
    ∃x:G,x∈c.T ∧ x∉Y ∧ x∈normalizer (Y:Set G) ∧ x^2∈Y ∧
      D.conjBy x⁻¹≠⊥ ∧ D.conjBy x⁻¹≤elementaryAbelianMaxJ Y⊓twoCore H ∧
      Y≤normalizer (D.conjBy x⁻¹:Set G) := by
  obtain ⟨V,hV,x,hxT,hxS,hxN,hx2,hm⟩:=
    MathieuSourceSetup.linear_four_square_moving_plane c hG hempty hgen e
  exact ⟨x,hxT,hxS,hxN,hx2,
    MathieuSourceSetup.linear_four_crossing_derived_core c hG hempty hgen e
      V hV x hxT hxS hxN hx2 hm⟩

theorem MathieuSourceSetup.derived_symplectic_selected_crossing_derived_core
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F)) :
    let Y:=(S:Subgroup H).map H.subtype
    let D:=⁅Y⊓L,Y⊓L⁆
    ∃x:G,x∈c.T ∧ x∉Y ∧ x∈normalizer (Y:Set G) ∧ x^2∈Y ∧
      D.conjBy x⁻¹≠⊥ ∧ D.conjBy x⁻¹≤elementaryAbelianMaxJ Y⊓twoCore H ∧
      Y≤normalizer (D.conjBy x⁻¹:Set G) := by
  obtain ⟨V,hV,x,hxT,hxS,hxN,hx2,hm⟩:=
    MathieuSourceSetup.derived_symplectic_square_moving_plane c hG hempty hgen F hn hF e
  exact ⟨x,hxT,hxS,hxN,hx2,
    MathieuSourceSetup.derived_symplectic_crossing_derived_core c hG hempty hgen F hn hF e
      V hV x hxT hxS hxN hx2 hm⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
