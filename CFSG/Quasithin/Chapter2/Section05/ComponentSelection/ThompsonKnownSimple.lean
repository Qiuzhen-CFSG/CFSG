module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ThompsonClassTwoSource
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete
/-! # Unconditional known-simple Thompson class-two boundary
The direct C.1.29 producer discharges the callback retained by the original
2.5.7 component source. The model hypotheses and all Sylow/conjugator maps
remain literal; this wrapper only supplies the proved local C.1.29 input.
Source: Aschbacher--Smith C.1.29 and 2.5.7, printed pp.554--556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.linear_simple_thompson_class_two_knownSimple
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    _root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
      center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)) :=
  MathieuSourceSetup.linear_simple_thompson_class_two c hG localC129Input_knownSimple hempty
    hgen F hn hF e x hxT hxS hxN hx2

theorem MathieuSourceSetup.linear_four_thompson_class_two_knownSimple
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    _root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
      center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)) :=
  MathieuSourceSetup.linear_four_thompson_class_two c hG localC129Input_knownSimple hempty
    hgen e x hxT hxS hxN hx2

theorem MathieuSourceSetup.derived_symplectic_thompson_class_two_knownSimple
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    _root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
      center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)) :=
  MathieuSourceSetup.derived_symplectic_thompson_class_two c hG localC129Input_knownSimple hempty
    hgen F hn hF e x hxT hxS hxN hx2
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
