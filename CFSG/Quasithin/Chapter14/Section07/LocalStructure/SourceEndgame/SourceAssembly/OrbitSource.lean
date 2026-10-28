module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.RudvalisSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits.EarlierThirteen

/-!
# The original Rudvalis endpoint with the orbit and span inputs discharged

The actual natural action and critical path prove 14.7.12–13, uniformly
for every permitted rechoice. These results supply the central, derived
and Frattini spans in the original 14.7.75 application. The same path
argument supplies its L-conjugacy clause after the genuine earlier
length-three implication. B.5 and original Type-Ru recognition are already
discharged by the imported source endpoint.

The independent critical-length, fusion, local structure and F-source
inputs remain explicit; no source group, selected path or quotient changes.
Source: Aschbacher–Smith 14.7.12–13 and 14.7.70–75.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt
open CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open SteinbergRecognition SteinbergRecognition.ModuleRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
    ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
  (sourceF : FSource.SourceClassificationInput KnownSimple.IsKnownSimple.{u})
include structural faithful amalgams sourceF

/-- The literal original-source Ru conclusion with no orbit or span premise. -/
theorem source_rudvalis_of_source_orbits
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (earlier_length : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V → c'.b = 3)
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) : Nonempty (G≃*Rudvalis.Model) := by
  apply source_rudvalis_of_theoremsAC d c structural faithful amalgams sourceF hA hC
    earlier selection h69 earlier1332 h68 hUH heven
  · intro c' hZ
    have hb := earlier_length c' hZ
    obtain ⟨l, hl, he⟩ := SourceOrbits.three_conjugate d structural c' hb
    refine ⟨hb, l⁻¹, L.inv_mem hl, ?_⟩
    simpa only [conjugate, inv_inv] using he
  · exact SourceOrbits.earlier_thirteen_reselect d structural c
  · exact hcentralizer68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
