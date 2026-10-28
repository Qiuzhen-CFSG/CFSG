module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SourceAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalAssembly

/-!
# Local source geometry in the nonbinary-natural classification consumer

The Chapter 11 package supplies the literal normalizer, radical and plane
inputs to `NonbinaryNaturalLocalInputs`. The same invariant flag and Cartan
are used throughout. The earlier component comparison, refinement, natural
seed and odd-extension index premises remain explicit; this adapter does not
assert their existence.

Source: Aschbacher--Smith 11.1.1--11.2.5 and 11.4.1--11.5.8,
printed pp.761--770 and 775--784, as used in 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G) (z : G)

/-- The Chapter 11 conclusions fill their exact Chapter 12 fields. The
remaining hypotheses are the component, shadow and closure source inputs. -/
theorem nonempty_localInputs_of_source_geometry
    (h : SourceGeometry D S c f X)
    (hearlier : Comparison.EarlierGeometry (ofFlag S f X z ⊥))
    (hlinear : Chapter11.Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (hcent : f.Vi 0 ≤ centralizer (f.Ri 0 : Set G))
    (hz : f.Vi 0 = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hKZ : (ofFlag S f X z ⊥).K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (href : Components.RefinementAlternative T L (f.Li 0) (f.Li 1)
      (ofFlag S f X z ⊥).K X 0 S.field.degree)
    (hflag : (ofFlag S f X z ⊥).ClosureFlag)
    (hseed : ∀ he : (ofFlag S f X z ⊥).K = (ofFlag S f X z ⊥).L₁,
      Nonempty (hflag.NaturalSeed he))
    (htorus : X ⊓ centralizer (f.Vi 0 : Set G) ≤ f.Li 0)
    (hcenter : center (f.Li 0 ⧸ pCore 2 (f.Li 0)) = ⊥)
    (hrank : 1 ≤ primeRank 3 (f.Li 0))
    (hmodel : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hsplit : L ⊓ normalizer (f.Vi 0 : Set G) = (f.Li 0 ⊔ L.pCoreIn 2) ⊔ X)
    (hfirst : Chapter11.Source.ComponentIn
      (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G)) (f.Li 0))
    (hindex : ∀ p : ℕ, S.field.degree = 2 → (p = 5 ∨ (p.Prime ∧ 11 ≤ p)) →
      Chapter11.Source.IsSL (Chapter11.Source.TwoOddQuotient (ofFlag S f X z ⊥).K) 2 p →
      (twoFittingCore ((ofFlag S f X z ⊥).K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
        (solvableRadical ((ofFlag S f X z ⊥).K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2) :
    Nonempty (NonbinaryNaturalLocalInputs S f X z) := by
  obtain ⟨P,hP⟩ := h.plane_data
  exact ⟨{
    earlier := hearlier
    sylow_normalizer := h.sylow_normalizer
    linear_fixed := hlinear
    radical_centralizes_point := hcent
    cartan_point := hz
    cartan := h.cartan
    cartan_normalizes_point := h.cartan_normalizes 0
    cartan_normalizes_radical := hXR
    component_centralizes_omega := hKZ
    refinement := href
    radical_normalizer := h.radical_alternative
    odd_kernel := h.odd_kernel
    maximal_unique := h.maximal_unique
    three_centralizer := h.three_centralizer
    fixed_line := h.fixed_line.le
    second_component := h.second_component
    flag_action := hflag
    natural_seed := hseed
    point_torus := htorus
    local_center := hcenter
    local_three_rank := hrank
    local_model := hmodel
    point_split := hsplit
    first_component := hfirst
    plane_sylow := P
    plane_fixed := hP
    plane_radical := h.plane_radical
    linear_movement := h.linear_movement
    fitting_index := hindex }⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
