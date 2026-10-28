module

public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.QuadraticSource
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization
public import Theory.Representation.BinaryOffender.OrderTwoComponentObstruction

/-!
# Applying quadratic four-group classification to the actual replacement

A moving best offender's literal displacement centralizer supplies the marked
four-group. Its cyclic alternative is excluded by the proved two-codimension
bound. The genuine GLS2 25.14 classifier then describes the actual orbit quotient
and every nontrivial section. In the moved-space setup, the centralizer condition
is discharged by the source commutator argument; offender minimality supplies
the normalizer alternative for the replacement.

Source: GLS volume 2, Chapter G, Theorem 26.24, Steps 2--4. The subsequent
normalizer-invariant natural-section construction and numerical contradiction
are separate from these proved source steps.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentNormalization.ReplacementSource
open Representation.QuadraticFourGroup
universe u v w
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The full quadratic source theorem applies to the actual replacement
four-group, with its original inclusion in the offender. -/
theorem exists_classified_fourGroup (hf : Function.Injective ρ)
    {A L : Subgroup G} (hA : IsBestOffender ρ A) (hL : IsComponent G L)
    {a : G} (ha : a ∈ A) (haN : a ∉ normalizer (L : Set G))
    (hcent : displacementCentralizer ρ A ⊓ centralizer (L : Set G) = ⊥)
    (halt : displacementCentralizer ρ A = A ∨
      displacementCentralizer ρ A ≤ normalizer (L : Set G)) :
    ∃ c ∈ displacementCentralizer ρ A, c ≠ 1 ∧ c ≠ a ∧
      ∃ B : Subgroup G, B = closure ({a,c} : Set G) ∧ B ≤ A ∧
        Hypotheses ρ L B a ∧
        ∃ M : TwoFactorModel (componentOrbit L B),
          ∀ (W : Type w) [AddCommGroup W] [Module (ZMod 2) W]
            [FiniteDimensional (ZMod 2) W]
            (σ : Representation (ZMod 2) (componentOrbit L B) W),
            IsIrreducibleSection (ρ.comp (componentOrbit L B).subtype) σ →
              σ.IsTrivial ∨ IsNaturalTensorAlong M.projection σ := by
  obtain ⟨c,hc,hc1,hca,B,hB,hBA,hBe,hcard,haB,_,hquad,hcentral⟩ :=
    hA.exists_fourGroup_of_moving_component ρ hf hL ha haN hcent halt
  let := hA.1.2
  have ha1 : a ≠ 1 := fun he => haN (he ▸ (normalizer (L : Set G)).one_mem)
  have h : Hypotheses ρ L B a := {
    faithful := hf
    component := hL
    elementary := hBe.2
    card_four := hcard
    mem := haB
    involution := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
    moves := fun he => haN (mem_normalizer_iff_map_conj_eq.mpr he)
    quadratic := hquad
    centralizer := hcentral }
  exact ⟨c,hc,hc1,hca,B,hB,hBA,h,QuadraticSource.classification h⟩

/-- Source Steps 2--4 in the actual moved-space minimal-counterexample setup.
The centralizer and replacement-normalizer premises are proved here. -/
theorem exists_classified_fourGroup_of_moved_space
    (hf : Function.Injective ρ) {A L : Subgroup G}
    (hA : IsBestOffender ρ A) (hL : IsComponent G L)
    (hAN : ¬ A ≤ normalizer (L : Set G))
    (hmin : ∀ C ≤ A, IsBestOffender ρ C → C = A ∨ C ≤ normalizer (L : Set G))
    (hV : Submodule.span (ZMod 2)
      (Set.range fun ev : componentOrbit L A × V => ρ ev.1 ev.2 - ev.2) = ⊤) :
    ∃ (a c : G), a ∈ A ∧ c ∈ displacementCentralizer ρ A ∧ c ≠ 1 ∧ c ≠ a ∧
      ∃ B : Subgroup G, B = closure ({a,c} : Set G) ∧ B ≤ A ∧
        Hypotheses ρ L B a ∧
        ∃ M : TwoFactorModel (componentOrbit L B),
          ∀ (W : Type w) [AddCommGroup W] [Module (ZMod 2) W]
            [FiniteDimensional (ZMod 2) W]
            (σ : Representation (ZMod 2) (componentOrbit L B) W),
            IsIrreducibleSection (ρ.comp (componentOrbit L B).subtype) σ →
              σ.IsTrivial ∨ IsNaturalTensorAlong M.projection σ := by
  let := hA.1.2
  have hEA := (hL.orbit_properties A hAN).2.2
  have hcent := displacementCentralizer_inf_centralizer_orbit_eq_bot ρ A L hf hEA hV
  have halt := hmin (displacementCentralizer ρ A) (displacementCentralizer_le ρ A)
    (hA.displacementCentralizer_isBestOffender ρ)
  obtain ⟨a,ha,_,haN,_,_⟩ := exists_moving_component_involution hA.1 hL hAN
  obtain ⟨c,hc,hc1,hca,B,hB,hBA,hq,M,hM⟩ :=
    exists_classified_fourGroup ρ hf hA hL ha haN hcent halt
  exact ⟨a,c,ha,hc,hc1,hca,B,hB,hBA,hq,M,hM⟩
end CFSG.Quasithin.ChapterB.ComponentNormalization.ReplacementSource
