module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.BlockClosure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.RootResidual

/-!
# Symplectic closure reduced to the nonbinary MS classification

The root-image branch now gives O₂(L)=V directly from the actual short
residual of IQ₁. Simplicity of the original symplectic quotient propagates
its core commutator bound to L. The full-image branch has every literal
MS-pair premise, so the nonbinary symplectic C.1.32 classification supplies
the remaining block. Both branches feed the full-cover terminal argument.

The only extra intermediate premise is the nonbinary symplectic MS
classification, requested from qt-c132-nonbinary-symplectic. Final discharge
and the unconditional source assembly remain with
qt-d-1222-natural-closure-sp4. The displayed remaining hypotheses are the
preceding flag, Cartan and local-component conclusions through 11.5.6.
Source: Aschbacher--Smith 11.5.7, pp.782--784, and C.1.32, pp.135--136.
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

include hpoint hthree hX hcartan hn3 hirr hti hgen hVX hfour hfive in
/-- The full-image branch only needs identification of the original core.
The separate root-image branch supplies that identification internally. -/
theorem abelian_of_preceding_and_core_recognition
    (p : Terminal.PointCoordinates E m)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hlocal₁ : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = pointLocal)
    (hlocal₂ : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = planeLocal)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₁ : ⁅V,E.L₁⁆ = E.V₃) (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hrecognition : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2) → L.pCoreIn 2 = V) :
    IsMulCommutative E.W := by
  have hc := commuting_of_preceding E m g hpoint hthree hX hcartan hn3 hirr hti
    hgen hVX hfour hfive p σ hlocal₁ hlocal₂ hunique hmoved₂
  by_contra hn
  obtain ⟨_,hW,hU,_,ha⟩ := CharacteristicBlock.msPair_reduction_of_preceding E m g
    hpoint hthree hX hcartan hn3 hirr hti hgen hVX hfour hfive hout hn
  have hcore : L.pCoreIn 2 = V := by
    rcases ha with hr | hms
    · exact CharacteristicBlock.root_case_core_eq_seed_of_preceding E m g hpoint hthree
        hX hcartan hn3 hirr hti hgen hVX hfour hfive hout hn hr
    · exact hrecognition hms
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact OppositeGeometry.cartan_normalizes_marked_flag E m hX 0
  obtain ⟨_,_,_,hroot,_⟩ := RadicalAction.initial_branch_of_preceding E m g hpoint
    hthree hcartan (hX.1.trans inf_le_left) hXG hn3 hirr hti hgen hVX hfour hfive hn
  have hroot' : actionImage (V := V) E.W ≤
      centralizer (actionImage (V := V) E.L₁ : Set (MulAut V)) := by
    have he : auxiliaryW E = E.W := by
      classical
      simp only [auxiliaryW,if_pos hc]
    rw [he] at hroot
    rw [hroot,map_center_subtype_eq_inf_centralizer]
    exact inf_le_right
  exact hn (Terminal.abelian_of_source_commuting E m hcore hU hc
    (Terminal.root_action_commutator_le_core E m hW hroot') hmoved₁ hti hgen hcontrol)

include hpoint hthree hX hcartan hn3 hirr hti hgen hVX hfour hfive in
/-- The original chosen closure is abelian once the genuine nonbinary
symplectic MS-pair classification is supplied. -/
theorem abelian_of_preceding_and_ms_recognition
    (p : Terminal.PointCoordinates E m)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hlocal₁ : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = pointLocal)
    (hlocal₂ : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = planeLocal)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₁ : ⁅V,E.L₁⁆ = E.V₃) (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hrecognition : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2) → ChapterC.IsSp4FourBlock L) :
    IsMulCommutative E.W := by
  apply abelian_of_preceding_and_core_recognition E m g hpoint hthree hX hcartan
    hn3 hirr hti hgen hVX hfour hfive p σ hlocal₁ hlocal₂ hunique hmoved₁ hmoved₂
    hcontrol hout
  intro hms
  exact core_eq_chosen_of_marked_sp4_block E m (hrecognition hms)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
