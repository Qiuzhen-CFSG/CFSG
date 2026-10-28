module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes.Comparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization.Consumers

/-!
# The trivial-covering-center branch of original 11.2.2(5--6)

The actual reciprocal-root family and full-plane residual generation force
every noncentral Vᵍ in T to normalize L when C_V(L)=1. Its inclusion in the
proved elementary full M-module is then a contradiction. Thus W₀(T,V)
centralizes V. The existing normalizer and R₁-localization arguments give
all accompanying bounds and the literal rank-one R₁ application.

Only the specified earlier-source uniqueness, flag and component clauses
remain explicit besides the stated branch condition C_V(L)=1. Their earlier
source producers and final local-geometry assembly retain their discharge.
The nonzero-center branch, with its full central extensions, remains with
qt-d-1222-natural-weak-closure-source; this file does not replace the general
public source statement by the trivial-center specialization.
Source: Aschbacher--Smith 11.2.2(5--6) and 11.5.1, printed pp.768,778.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
open Subgroup Representation Representation.BinaryOffender
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (localResidual L (f.Vi 1)))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)

include hunique hthree hline hcomponent hc in
/-- The original zeroth weak closure centralizes V in the trivial-center branch. -/
theorem source_zero_centralizes_of_central_eq_bot :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  refine le_inf (indexedWeakClosure_le V (T : Subgroup G) 0) ?_
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g,rfl,hg⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  by_contra hnon
  have hcomm : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro he
    exact hnon (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans he))
  obtain ⟨u,a,hact,-,ha,hroots⟩ :=
    ReciprocalRoots.source_root_family D S m f hunique hthree hline g hg hcomm
  have hgM := mem_normalizer_of_covering_center_absorption D S m f hcomponent u g a hact ha hroots
    (fun _ _ => by rw [hc,Subgroup.map_bot]; exact bot_le)
  let W := componentOrbit V (normalizer (L : Set G))
  let : IsElementaryAbelian 2 W := Preliminary.fullModule_elementary D S
  have hVW : V ≤ W := le_componentOrbit V _
  have hAW : V.map (MulAut.conj g).toMonoidHom ≤ W :=
    le_iSup_of_le (⟨g,hgM⟩ : normalizer (L : Set G)) le_rfl
  exact hnon (hAW.trans ((Subgroup.le_centralizer W).trans (Subgroup.centralizer_le hVW)))

include hunique hthree hline hcomponent hc in
/-- All G₂ closure and normalizer clauses on the original flag and residual R₁. -/
theorem source_clauses_of_central_eq_bot :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ normalizer (L : Set G) ∧
      0 < globalW V (T : Subgroup G) ∧
      centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G) ∧
      indexedWeakClosure V (f.Ri 0) 0 = indexedWeakClosure V (T : Subgroup G) 0 ∧
      normalizer (indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤ normalizer (L : Set G) := by
  have hw := source_zero_centralizes_of_central_eq_bot D S m f hunique hthree hline hcomponent hc
  obtain ⟨hN,hwpos,heq,hNR⟩ := normalizer_bounds_of_zero_centralizes D S f hw
  exact ⟨hw,hN,hwpos,Localization.source_clause_six_of_preceding D S m f hunique hthree hline,
    heq,hNR⟩

include hunique hthree hline hcomponent hc in
/-- The literal rank-one consumer with the weak-closure premise discharged. -/
theorem rankOne_impossible_of_central_eq_bot
    (H₁ : Subgroup G) (P : Sylow 2 H₁)
    (hP : (P : Subgroup H₁).map H₁.subtype = f.Ri 0)
    (hn : generationParameter H₁ = 1) (hout : ¬ H₁ ≤ normalizer (L : Set G)) : False :=
  Localization.rankOne_impossible_of_preceding_and_zero_centralizes D S m f hunique hthree hline
    (source_zero_centralizes_of_central_eq_bot D S m f hunique hthree hline hcomponent hc)
    H₁ P hP hn hout
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
