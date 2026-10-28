module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.Commuting
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.Moving
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.PlaneGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.RadicalGeometry

/-!
# Both terminal branches of the symplectic closure

Both branches use the literal chosen seed and flag. The commuting branch
propagates the L₁ commutator bound to its G₁-closure and applies the actual
KYM₁ supplement. The noncommuting branch identifies the intersection plane,
rechooses its transporter in N_G(V₂), and uses the genuine noncentral
component uniqueness assertion before comparing the two radical actions.

`abelian_of_source_geometry` discharges both the crossing-plane and
radical-displacement premises using the preceding marked point coordinates
and compatible images of the two local residuals. Thus neither terminal
branch nor its geometric conclusion is assumed. The lower-level
`abelian_of_terminal_inputs` remains available with its original interface.

The earlier source hypotheses remain explicit: the core identification,
initial core bound, abelian U, the genuine noncentral-component uniqueness,
the local commutator identities, TI, the supplement and normalizer control,
and the original root-action conclusion. In particular this is the terminal
part of 11.5.7, not a discharge of its preceding source arguments. The point
and local-residual markings belong to the preceding flag geometry; the
parent closure assembly must supply them and the fixed-space identity.
Source: Aschbacher--Smith 11.5.7, printed pp.783--784.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Conditional assembly with all additional action and geometry premises
visible. No final branch or closure conclusion is among the inputs. -/
theorem abelian_of_terminal_inputs (m : MarkedFlag E)
    (p : CrossingPlanes E) (r : RadicalDisplacement E)
    (hcore : L.pCoreIn 2 = V) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hU : IsMulCommutative E.U)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₁ : ⁅V,E.L₁⁆ = E.V₃) (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hTI : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M)
    (hroot : ¬ IsMulCommutative E.W → ⁅V,E.U⁆ = ⊥ →
      actionImage (V := V) E.W ≤ centralizer (actionImage (V := V) E.L₁ : Set (MulAut V))) :
    IsMulCommutative E.W := by
  by_contra hn
  by_cases hc : ⁅V,E.U⁆ = ⊥
  · exact hn (abelian_of_source_commuting E m hcore hU hc
      (root_action_commutator_le_core E m hW (hroot hn hc)) hmoved₁
      hTI hgen hcontrol)
  · exact noncommuting_impossible E m p r hW hunique hmoved₂ hc

/-- The noncommuting terminal branch with both model calculations discharged.
The point coordinates use the original marked action on V, and one common
reorientation identifies both literal local residuals in L/O₂(L). -/
theorem noncommuting_impossible_of_source_geometry (m : MarkedFlag E)
    (p : PointCoordinates E m) (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hcore : L.pCoreIn 2 = V)
    (σ : MulAut (Theory.SpecificGroups.SymplecticFour.Sp E.input.field.Carrier))
    (hpoint : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) =
        Theory.SpecificGroups.SymplecticFour.pointLocal)
    (hplane : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) =
        Theory.SpecificGroups.SymplecticFour.planeLocal)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved : ⁅V,E.L₂⁆ = V) (hne : ⁅V,E.U⁆ ≠ ⊥) : False :=
  noncommuting_impossible E m (p.crossingPlanes hc hW)
    (radicalDisplacement_of_local_marking m hcore σ hpoint hplane)
    hW hunique hmoved hne

/-- Both terminal branches of source 11.5.7 under its preceding geometric
and action inputs. The plane alignment, reverse plane, transporter rechoice
and radical separation are proved internally. Neither K=L₁, W_H=UV,
CrossingPlanes, RadicalDisplacement nor a final branch is a hypothesis. -/
theorem abelian_of_source_geometry (m : MarkedFlag E)
    (p : PointCoordinates E m) (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hcore : L.pCoreIn 2 = V)
    (σ : MulAut (Theory.SpecificGroups.SymplecticFour.Sp E.input.field.Carrier))
    (hpoint : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) =
        Theory.SpecificGroups.SymplecticFour.pointLocal)
    (hplane : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) =
        Theory.SpecificGroups.SymplecticFour.planeLocal)
    (hW : E.W ≤ E.G₁.pCoreIn 2) (hU : IsMulCommutative E.U)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₁ : ⁅V,E.L₁⁆ = E.V₃) (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hTI : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M)
    (hroot : ¬ IsMulCommutative E.W → ⁅V,E.U⁆ = ⊥ →
      actionImage (V := V) E.W ≤ centralizer (actionImage (V := V) E.L₁ : Set (MulAut V))) :
    IsMulCommutative E.W :=
  abelian_of_terminal_inputs E m (p.crossingPlanes hc hW)
    (radicalDisplacement_of_local_marking m hcore σ hpoint hplane)
    hcore hW hU hunique hmoved₁ hmoved₂ hTI hgen hcontrol hroot

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
