module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.SylowFacts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal.Factors
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal.Intersections
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal.ComponentNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal.CoreFixed

/-!
# Assembly of the marked five-local configuration

The exact subgroup Y = P ∩ E(C_G(E)) has order five and complements E in P.
The inverter supplied by the root-family witness acts on E, while an
involution in its actual A₅ component acts on Y. The split-extension
calculation gives the literal intersections with C_G(W.inverter).

The core fixed subgroup is the marked involution line, as proved in
`CoreFixed`, and `ComponentNormalizer` supplies the normalizer and inverter
inside the marked A₅ component. Its internal centralizer is determined by
the self-centralization of P. Combining these results constructs `LocalData`
from the root-five witness, with no extra core or component premise. The
existence application chooses a root-family member in each Sylow subgroup.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2, printed p.261,
the paragraph beginning with Y = P ∩ E(M).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {E : Subgroup G}

/-- Conditional assembly of the marked configuration. The two inputs
are the fixed subgroup in the extraspecial core and the internal A₅ calculation;
`localData_of_marked_intersection` discharges both. -/
theorem localData_of_core_and_component (hG : Nat.card G = 604800)
    (hE : Nat.card E = 5) (W : RootFiveWitness D E) (P : Sylow 5 G)
    (hEP : E ≤ (P : Subgroup G))
    (hQ : ambientCore W.inverter ⊓
      centralizer (((P : Subgroup G) ⊓ fiveComponent E : Subgroup G) : Set G) =
        zpowers W.inverter)
    (hN : ∃ t ∈ fiveComponent E, orderOf t = 2 ∧
      (∀ y ∈ (P : Subgroup G) ⊓ fiveComponent E, t * y * t⁻¹ = y⁻¹) ∧
      fiveComponent E ⊓ normalizer (((P : Subgroup G) ⊓ fiveComponent E : Subgroup G) : Set G) =
        ((P : Subgroup G) ⊓ fiveComponent E) ⊔ zpowers t) :
    Nonempty (LocalData E ((P : Subgroup G) ⊓ fiveComponent E) P W.inverter) := by
  obtain ⟨t, htL, ht, hti, htN⟩ := hN
  have hC := component_intersection_centralizer hG hE W P hEP
  have hlocal := local_intersections W _ inf_le_right t hQ hC htN
  exact ⟨{
    card_E := hE
    card_Y := intersection_card hG W P hEP
    product := intersection_product hG hE W P hEP
    disjoint := (disjoint_E_component W).mono_right inf_le_right
    involution_z := inverter_order W
    centralizes_Y := inf_le_right.trans W.component_le
    inverts_E := W.inverts
    t := t
    involution_t := ht
    commutes := (mem_centralizer_singleton_iff.mp (W.component_le htL)).symm
    centralizes_E := fun x hx => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (component_centralizes_E htL) x hx)
    inverts_Y := hti
    local_centralizer := hlocal.1
    local_normalizer := hlocal.2 }⟩

/-- The marked intersection has the full local configuration of 47.2.

The two premises of the conditional assembly are discharged by the literal
extraspecial-core fixed-point calculation and the marked A₅ normalizer
calculation. Thus `Y` remains the actual subgroup
`P ⊓ fiveComponent E`, with the inverter and component supplied by `W`. -/
theorem localData_of_marked_intersection (hG : Nat.card G = 604800)
    (hE : Nat.card E = 5) (W : RootFiveWitness D E) (P : Sylow 5 G)
    (hEP : E ≤ (P : Subgroup G)) :
    Nonempty (LocalData E ((P : Subgroup G) ⊓ fiveComponent E) P W.inverter) := by
  exact localData_of_core_and_component hG hE W P hEP
    (CoreFixed.intersection_core_fixed hG W P hEP)
    (component_intersection_normalizer hG W P hEP)

/-- Conditional application selecting a root member in each Sylow subgroup.
The core and component premises are discharged in `exists_localData`. -/
theorem exists_localData_of_core_and_component (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D) (hA : RootFiveFamily D S.t)
    (hcore : ∀ (E : Subgroup G) (W : RootFiveWitness D E) (Y : Subgroup G),
      Y ≤ fiveComponent E → Nat.card Y = 5 →
      ambientCore W.inverter ⊓ centralizer (Y : Set G) = zpowers W.inverter)
    (hcomponent : ∀ (E : Subgroup G) (_W : RootFiveWitness D E) (Y : Subgroup G),
      Y ≤ fiveComponent E → Nat.card Y = 5 →
      ∃ t ∈ fiveComponent E, orderOf t = 2 ∧
        (∀ y ∈ Y, t * y * t⁻¹ = y⁻¹) ∧
        fiveComponent E ⊓ normalizer (Y : Set G) = Y ⊔ zpowers t)
    (P : Sylow 5 G) :
    ∃ (E : Subgroup G), FiveCentralizing S.t E ∧ E ≤ (P : Subgroup G) ∧
      ∃ W : RootFiveWitness D E,
        Nonempty (LocalData E ((P : Subgroup G) ⊓ fiveComponent E) P W.inverter) := by
  obtain ⟨E, hE, hEP⟩ := exists_root_member_in_sylow S P
  obtain ⟨W⟩ := hA E hE
  have hY := intersection_card hG W P hEP
  have hc := hcore E W _ inf_le_right hY
  have hN := hcomponent E W _ inf_le_right hY
  exact ⟨E, hE, hEP, W, localData_of_core_and_component hG hE.1 W P hEP hc hN⟩

/-- Every Sylow five-subgroup receives the marked local configuration once the
root-five family is available. -/
theorem exists_localData (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D) (hA : RootFiveFamily D S.t)
    (P : Sylow 5 G) :
    ∃ (E : Subgroup G), FiveCentralizing S.t E ∧ E ≤ (P : Subgroup G) ∧
      ∃ W : RootFiveWitness D E,
        Nonempty (LocalData E ((P : Subgroup G) ⊓ fiveComponent E) P W.inverter) := by
  obtain ⟨E, hE, hEP⟩ := exists_root_member_in_sylow S P
  obtain ⟨W⟩ := hA E hE
  exact ⟨E, hE, hEP, W, localData_of_marked_intersection hG hE.1 W P hEP⟩
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal
