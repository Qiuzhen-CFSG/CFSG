module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ThompsonClassTwoSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearFrattiniSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticFrattiniSource
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete
/-! # Original crossing preparation and marked quotients
The proved C.1.29 source discharges the original crossing preparation: nontrivial core Frattini subgroup, class two, and the core Thompson identity.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
omit [Finite G] in
private theorem ambient_core_frattini_ne_bot
    (h:frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)≠⊥) :
    frattini (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H:Subgroup G)≠⊥ := by
  let C:=(elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)
  have hmap:C.map H.subtype=elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H:=by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective]
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    rfl
  let e:=((C.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hmap))
  intro hh
  apply h
  apply bot_unique
  intro c hc
  have hm:e c∈frattini (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H:Subgroup G):=by
    rw [←frattini_map_equiv e]
    exact mem_map_of_mem e.toMonoidHom hc
  rw [hh,mem_bot] at hm
  exact e.injective (hm.trans e.map_one.symm)

theorem MathieuSourceSetup.linear_simple_crossing_preparation_knownSimple
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    frattini (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H:Subgroup G)≠⊥ ∧
      (_root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
        center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))) ∧
      elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H=elementaryAbelianMaxJ (twoCore H) := by
  refine ⟨ambient_core_frattini_ne_bot
    (MathieuSourceSetup.linear_simple_thompson_core_frattini_ne_bot c hG localC129Input_knownSimple hempty hgen F hn hF e),?_,?_⟩
  · exact MathieuSourceSetup.linear_simple_thompson_class_two c hG localC129Input_knownSimple hempty hgen F hn hF e x hxT hxS hxN hx2
  · exact MathieuSourceSetup.linear_simple_thompson_core c hG localC129Input_knownSimple hempty hgen F hn hF e

theorem MathieuSourceSetup.linear_four_crossing_preparation_knownSimple
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    frattini (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H:Subgroup G)≠⊥ ∧
      (_root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
        center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))) ∧
      elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H=elementaryAbelianMaxJ (twoCore H) := by
  refine ⟨ambient_core_frattini_ne_bot
    (MathieuSourceSetup.linear_four_thompson_core_frattini_ne_bot c hG localC129Input_knownSimple hempty hgen e),?_,?_⟩
  · exact MathieuSourceSetup.linear_four_thompson_class_two c hG localC129Input_knownSimple hempty hgen e x hxT hxS hxN hx2
  · exact MathieuSourceSetup.linear_four_thompson_core c hG localC129Input_knownSimple hempty hgen e

theorem MathieuSourceSetup.derived_symplectic_crossing_preparation_knownSimple
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    frattini (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H:Subgroup G)≠⊥ ∧
      (_root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
        center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))) ∧
      elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H=elementaryAbelianMaxJ (twoCore H) := by
  refine ⟨ambient_core_frattini_ne_bot
    (MathieuSourceSetup.derived_symplectic_thompson_core_frattini_ne_bot c hG localC129Input_knownSimple hempty hgen F hn hF e),?_,?_⟩
  · exact MathieuSourceSetup.derived_symplectic_thompson_class_two c hG localC129Input_knownSimple hempty hgen F hn hF e x hxT hxS hxN hx2
  · exact MathieuSourceSetup.derived_symplectic_thompson_core c hG localC129Input_knownSimple hempty hgen F hn hF e
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
