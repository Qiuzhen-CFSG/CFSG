module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Recognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.QuotientGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer

/-!
# The root-four five-centralizer recognition branch

The selected 47.1 geometry proves the involution conjugacy and full
centralizer data for the literal quotient C_G(E)/E. The checked A₄/A₅
recognition theorem, together with five dividing its order, identifies this
quotient with A₅. The central extension splits over the actual quotient map.

The marked normalizer construction then gives N_G(E) ≃ D₁₀ × A₅, with
the intrinsic component, generation by the orbit of the original seed,
and an inverting conjugate of z marking the factors. It also supplies the
component's internal complement to the ambient core in that inverter's
centralizer. `rootFiveFamily_of_selectedGeometry` assembles every field
without further premises beyond the seed, order and selected 47.1 geometry.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent

variable {G : Type*} [Group G] [Finite G]

/-- The geometric family yields actual quotient models for every source five-subgroup.
The local involution representative is transported within its ambient conjugacy class. -/
theorem quotient_models_of_involution_family {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (hG : Nat.card G = 604800)
    (I : QuotientInvolutionFamily S.t) (E : Subgroup G) (hE : FiveCentralizing S.t E) :
    Nonempty (Quotient E ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨u, htu, hEu, ⟨localData⟩⟩ := I E hE
  have hu : orderOf u = 2 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp htu
    exact ((MulAut.conj g).orderOf_eq S.t).trans S.other.1
  exact quotient_equiv_of_involutionData hG E hE.1 u hu hEu localData

/-- Recognition feeds the actual splitting theorem, retaining the quotient map
and the internal complement used by the marked normalizer construction. -/
theorem centralizer_splits_of_involution_family {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (hG : Nat.card G = 604800)
    (I : QuotientInvolutionFamily S.t) (E : Subgroup G) (hE : FiveCentralizing S.t E) :
    ∃ e : Quotient E ≃* alternatingGroup (Fin 5),
      ∃ s : alternatingGroup (Fin 5) →* centralizer (E : Set G),
        (e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))).comp s = MonoidHom.id _ ∧
          (kernel E).IsComplement' s.range := by
  obtain ⟨e⟩ := quotient_models_of_involution_family S hG I E hE
  obtain ⟨s, hs, hc⟩ := exists_complement_of_quotient_equiv E hE.1 e
  exact ⟨e, s, hs, hc⟩

/-- The root-four branch of 47.2(2), conditional only on the earlier 47.1
geometry and order. The quotient involution geometry discharges recognition;
the resulting models supply every marked normalizer, generation, inverter
and internal-complement field for the entire source five-family. -/
theorem rootFiveFamily_of_selectedGeometry {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (hG : Nat.card G = 604800) :
    RootFiveFamily D S.t := by
  exact MarkedNormalizer.rootFiveFamily_of_quotient_models S
    (quotient_models_of_involution_family S hG
      (quotientInvolutionFamily_of_selectedGeometry S))

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent
