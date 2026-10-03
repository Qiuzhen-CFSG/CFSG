module
public import Stellmacher.SectionEight.EightSixCostFourCubicOrbit
public import Theory.GroupAction.CubicOrbitCommutator
/-!
# The canonical cost-four initial residual module

In the actual selected cost-four configuration, W=[U,Ea], where U is the
selected E-closure of the initial center, is elementary abelian of order
sixteen. It contains U, lies in the initial pair, and is normalized by Q
and the initial residual. An actual order-three element of that residual
fixes only the identity of W.

The native cubic-orbit theorem constructs U∨Uᵗ with these properties.
The cubic norm commutator theorem identifies this orbit support with
[U,⟨t⟩]. Since t belongs to Ea, that subgroup lies in [U,Ea]. Conversely,
Ea normalizes the orbit support containing U, so [U,Ea] lies in it.
The equality transports every structural and fixed-point conclusion.

Source: Stellmacher (8.6)(b3), printed p.44. This is the actual canonical
subgroup used in the normalizer obstruction; no symmetric-group quotient
or abstract representation is assumed.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_cost_four_initial_residual_module
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
    let W := ⁅U,EAt ctx.Γ ctx.criticalPath.a⁆
    IsElementaryAbelianSubgroup 2 W ∧ Nat.card W = 16 ∧ U ≤ W ∧
      W ≤ (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ∧
      Q ≤ Subgroup.normalizer (W : Set G) ∧
      EAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.normalizer (W : Set G) ∧
      ∃ t : G, t ∈ EAt ctx.Γ ctx.criticalPath.a ∧ orderOf t = 3 ∧
        W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  classical
  let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
  let F := EAt ctx.Γ ctx.criticalPath.a
  obtain ⟨t,htF,ht3,helem,hcardW,hWR,hQN,hFN,hfixed⟩ :=
    eight_six_cost_four_cubic_orbit ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  let W0 := U ⊔ U.conjBy t
  have hUW : U ≤ W0 := le_sup_left
  have hT : Subgroup.zpowers t ≤ F := Subgroup.zpowers_le.mpr htF
  have horbit : W0 = ⁅U,Subgroup.zpowers t⁆ :=
    Subgroup.cubic_orbit_eq_commutator U t (ht3 ▸ pow_orderOf_eq_one t)
      helem (hFN htF) hfixed
  have hcomm : ⁅U,F⁆ = W0 := by
    apply le_antisymm
    · exact (Subgroup.commutator_mono hUW le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hFN)
    · rw [horbit]
      exact Subgroup.commutator_mono le_rfl hT
  change IsElementaryAbelianSubgroup 2 ⁅U,F⁆ ∧ _
  rw [hcomm]
  exact ⟨helem,hcardW,hUW,hWR,hQN,hFN,t,htF,ht3,hfixed⟩
end Stellmacher.SectionEight
