module
public import Stellmacher.SectionEight.EightSixSelectedResidualCostSquare
public import Stellmacher.SectionThree.CentralCoatomCentralDisplacement
/-!
# Square powers for actual selected coatom costs

For the selected large-index local configuration, every actor in the actual
coatom A0 has original commutator cost 2^(2*n). All selected hypotheses,
including the real Q=O₂(L), are retained; no numerical branch or raw action
recognition is assumed.

The literal residual-fixed quotient Vnext/C is elementary. Its action of E
has two conjugate generators, central coatom image, no residual fixed
vectors, and involutory selected actor, by the shared actual action packet.
The central-coatom square-power theorem applies to each coatom actor's
actual cyclic displacement. Native quotient commutator cardinality and
source-(14) exact cost transfer identify it with the original Vnext/Znext
cost. This is the square-power ingredient of Stellmacher (8.6), assertion
(17), printed p.44 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u
public theorem eight_six_selected_coatom_cost_square
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
    (hQ : Q = twoCoreIn L) (mover : G) (hmover : mover ∈ A0) :
    ∃ n : ℕ, eightSixCommutatorCost ctx.Γ ctx.criticalPath mover = 2 ^ (2 * n) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hA0A : A0 ≤ A := geom.coatom_eq ▸ inf_le_left
  let a : E := ⟨actor,hAE ha⟩
  let x : E := ⟨geom.x,twoResidualIn_le E geom.residual_mem⟩
  let b : E := ⟨mover,hAE (hA0A hmover)⟩
  let Ai := A.subgroupOf E
  let A0i := A0.subgroupOf E
  obtain ⟨hN,hW,action,haction,hkernel,hfixed⟩ := eight_six_residual_fixed_quotient_module
    ctx hcenter hlength hcard data.first_commutator E geom.group_le
  let _ := hN
  let _ := hW
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  obtain ⟨hgen,hAi,hA0two,hcentral,hsquares⟩ := eight_six_selected_coatom_action_data
    ctx previous D L Q hD hQ data E A0 actor geom ha action hkernel
  obtain ⟨n,hn⟩ := SectionThree.central_coatom_displacement_card_is_square_power
    action Ai A0i a x hgen hAi hA0two hcentral hfixed (hsquares a ha) b hmover
  have hcyclic : (Subgroup.zpowers mover).subgroupOf E = Subgroup.zpowers b := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr (hAE (hA0A hmover))),
      MonoidHom.map_zpowers]
    rfl
  have hAV : ⁅V,Subgroup.zpowers mover⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr (hAE (hA0A hmover))).trans hEV)
  have hrel := Subgroup.relIndex_sup_right
    ((⁅V,Subgroup.zpowers mover⁆).subgroupOf V) (C.subgroupOf V)
  rw [←Subgroup.subgroupOf_sup hAV inf_le_left,
    Subgroup.relIndex_subgroupOf (sup_le hAV inf_le_left),
    Subgroup.relIndex_subgroupOf hAV] at hrel
  have hrank : Nat.card (commutatorAction (Subgroup.zpowers (action b))
      (V ⧸ C.subgroupOf V)) = C.relIndex (⁅V,Subgroup.zpowers mover⁆ ⊔ C) := by
    have hh := Subgroup.quotient_conjugation_commutatorAction_card E V C
      (Subgroup.zpowers mover) hEV (Subgroup.zpowers_le.mpr (hAE (hA0A hmover))) hN action haction
    rw [hcyclic,MonoidHom.map_zpowers] at hh
    exact hh.trans hrel.symm
  have hfixedCore := (eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin).1
  have hcostTransfer := (eight_six_selected_cost_residual_transfer ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hfixedCore mover
      (hA0A hmover)).2
  exact ⟨n,hcostTransfer.trans (hrank.symm.trans hn)⟩
end Stellmacher.SectionEight
