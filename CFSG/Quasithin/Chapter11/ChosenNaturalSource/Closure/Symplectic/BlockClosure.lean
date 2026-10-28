module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CoreAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.Cover

/-!
# Symplectic closure after the characteristic-block reduction

The initial source argument supplies the two-core bounds and abelian U.
The full-cover terminal calculation excludes [V,U] ≠ 1 without any block
premise. In the surviving commuting branch, the Sp₄(4)-block and the genuine
multiplier equality identify O₂(L) with the original V. The literal root
image then bounds [W_H,L₁], and the preceding supplement and normalizer
control prove W_H=UV and hence abelianness.

Only the characteristic-block recognition remains an intermediate input
here. Its discharge is retained by qt-d-1222-natural-closure-sp4. The other
explicit hypotheses are the preceding flag, Cartan and local-component
geometry and source conclusions through 11.5.6. No triviality of C_V(L),
replacement module, K=L₁, or H¹ vanishing is used.

Source: Aschbacher--Smith 11.5.7, printed pp.782--784.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)

include m hX in
private theorem cartan_le_point_normalizer : E.X ≤ E.G₁ := by
  change E.X ≤ normalizer (E.V₁ : Set G)
  rw [m.point_preimage]
  exact OppositeGeometry.cartan_normalizes_marked_flag E m hX 0

include hpoint hthree hX hcartan hn3 hirr hti hgen hVX hfour hfive in
/-- The noncommuting source branch is excluded before block recognition. -/
theorem commuting_of_preceding
    (p : Terminal.PointCoordinates E m)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hlocal₁ : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = pointLocal)
    (hlocal₂ : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = planeLocal)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₂ : ⁅V,E.L₂⁆ = V) : ⁅V,E.U⁆ = ⊥ := by
  obtain ⟨_,hW,_⟩ := RadicalAction.initial_bounds_and_U_abelian E m g hpoint hthree
    hcartan (hX.1.trans inf_le_left) (cartan_le_point_normalizer E m hX)
    hn3 hirr hti hgen hVX hfour hfive
  by_contra hc
  exact Terminal.noncommuting_impossible_cover m p
    (Terminal.radicalDisplacement_cover m σ hlocal₁ hlocal₂) hW hunique hmoved₂ hc

include hpoint hthree hX hcartan hn3 hirr hti hgen hVX hfour hfive in
/-- The characteristic block is the sole remaining intermediate premise of
the original closure abelianness argument. -/
theorem abelian_of_preceding_and_block
    (p : Terminal.PointCoordinates E m)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hlocal₁ : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = pointLocal)
    (hlocal₂ : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = planeLocal)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₁ : ⁅V,E.L₁⁆ = E.V₃) (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M)
    (hb : ChapterC.IsSp4FourBlock L) : IsMulCommutative E.W := by
  have hc := commuting_of_preceding E m g hpoint hthree hX hcartan hn3 hirr hti
    hgen hVX hfour hfive p σ hlocal₁ hlocal₂ hunique hmoved₂
  by_contra hn
  obtain ⟨_,hW,hU,hroot,_⟩ := RadicalAction.initial_branch_of_preceding E m g hpoint
    hthree hcartan (hX.1.trans inf_le_left) (cartan_le_point_normalizer E m hX)
    hn3 hirr hti hgen hVX hfour hfive hn
  have hroot' : actionImage (V := V) E.W ≤
      centralizer (actionImage (V := V) E.L₁ : Set (MulAut V)) := by
    have he : auxiliaryW E = E.W := by
      classical
      simp only [auxiliaryW,if_pos hc]
    rw [he] at hroot
    rw [hroot,map_center_subtype_eq_inf_centralizer]
    exact inf_le_right
  have hcore := core_eq_chosen_of_marked_sp4_block E m hb
  exact hn (Terminal.abelian_of_source_commuting E m hcore hU hc
    (Terminal.root_action_commutator_le_core E m hW hroot') hmoved₁ hti hgen hcontrol)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
