module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Noncentral
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Even
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# The source Frattini action for every field degree

The completed component sieve fixes every C-component with quasisimple
two-core quotient. In odd degree its only surviving row would have nilpotent
F*, whereas a quasisimple group equals its own F*. In even degree the
constructed Suzuki movement argument already fixes all C-components.
The quotient-layer criterion then proves 11.5.6(4) without an assumption
about the surviving nonquasisimple SL₂(5) extensions in 11.5.6(3).

Only original preceding flag, Cartan and local-centralizer geometry remains;
qt-d-1222-natural-closure and its preceding geometry producers retain its
discharge. The literal clause (3) and the final closure assembly remain with
qt-d-1222-natural-closure-cartan. The symplectic consumer is in
`CartanCore.Symplectic`.
Source: Aschbacher--Smith 11.5.6(2--5), printed pp.780--781.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)
/-- In odd degree the remaining nilpotent-Fitting row cannot be quasisimple. -/
theorem quasisimple_component_commutator_of_odd_marked (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hsimple : IsQuasisimple (I ⧸ pCore 2 I)) :
    ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2 := by
  by_contra hmoved
  obtain ⟨hnil,_,_⟩ := E.moved_component_nilpotent_fitting_case hp hT hX c
    hcart hXR hCX hz hNG hr hodd hI hmoved
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  let eI : I.subgroupOf E.G₁ ≃* I := subgroupOfEquivOfLe (hI.1.trans E.Y_le_G₁)
  let eQ : (I ⧸ pCore 2 I) ≃* B :=
    (QuotientGroup.congr _ _ eI (pCore_map_iso 2 eI)).symm.trans
      (cComponentTwoCoreQuotientEquiv (E.component_in_point_normalizer hI))
  let : IsQuasisimple (I ⧸ pCore 2 I) := hsimple
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eQ
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  let : Group.IsNilpotent (generalizedFitting B) := hnil.2.1
  let : Group.IsNilpotent B := Group.nilpotent_of_mulEquiv
    ((MulEquiv.subgroupCongr (generalizedFitting_eq_top_of_quasisimple (G := B))).trans topEquiv)
  exact Group.IsPerfect.not_isNilpotent B inferInstance

/-- Source 11.5.6(4), with the rank bound from (2) explicit, for either parity. -/
theorem cartan_frattini_action_of_small_rank (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1)
    (P : Subgroup G) (hP : P ≤ T) (hPX : P = ⁅P,E.X⁆)
    (hphi : (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2) :
    ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2 := by
  by_cases he : Even E.input.field.degree
  · exact (E.cartan_actions_of_even_marked hp hT hX c hcart hXR hCX hz hNG he).2
      P hP hPX hphi
  · apply E.frattini_action_of_quasisimple_component_actions hp hT hX hcart.odd
      (fun I hI hs => E.quasisimple_component_commutator_of_odd_marked hp hT hX c
        hcart hXR hCX hz hNG hr (Nat.not_even_iff_odd.mp he) hI hs) P hP hPX hphi

/-- Source 11.5.6(4) from preceding marked geometry. The Cartan ranks and the
three-rank bound of Y are derived, and no component-action premise remains. -/
theorem cartan_frattini_action_of_marked (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hthree : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    (P : Subgroup G) (hP : P ≤ T) (hPX : P = ⁅P,E.X⁆)
    (hphi : (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2) :
    ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2 := by
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  exact E.cartan_frattini_action_of_small_rank hp hT hX c hcart hXR hCX hz hNG
    (E.three_rank_Y_le_one hp hc hexception hz hthree) P hP hPX hphi

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
