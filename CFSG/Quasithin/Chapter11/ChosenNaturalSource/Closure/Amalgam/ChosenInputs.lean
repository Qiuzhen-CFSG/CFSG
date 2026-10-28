module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Setup
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Discharging the local F.7 inputs on the original chosen module

The proved uniqueness theorem 1.2.7 supplies the unique maximal two-local
over LT. The genuine FSU theorem 3.2.2(8), transported using the unchanged
seed, supplies reducedness and C_T(V)=O₂(LT). Even characteristic gives
F*(LT)=O₂(LT). Only T-invariance of the field line, its local centralizer
bound, and centralization by K remain explicit in LocalInputs.

Source: Aschbacher--Smith, 11.5.8, printed p.784, using 1.2.7, 3.2.2(8),
and the field flag of 11.1. No characteristic-two, reducedness, or centralizer
conclusion is assumed as extra input.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- Construct the local amalgam inputs from the original chosen module and
the preceding point-centralizer geometry. -/
theorem localInputs_of_point_geometry
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hpoint : LT E ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁ ⊔ (T : Subgroup G))
    (hK : E.K ≤ centralizer (E.V₁ : Set G)) : LocalInputs E := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    E.input.source.simpleQTKE T E.input.source.maximal_faithful.1
  have hr := (D.fundamentalSetup E.input.source.toHypothesis1221).module_reduced hu
  have hc := (D.fundamentalSetup E.input.source.toHypothesis1221).sylow_centralizer_module hu
  rw [E.input.unchanged_seed] at hr hc
  change IsPReduced 2
    (V.subgroupOf (Chapter3.Section02.localOrbit T L ⊔ (T : Subgroup G))) at hr
  change (T : Subgroup G) ⊓ centralizer (V : Set G) =
    (Chapter3.Section02.localOrbit T L ⊔ (T : Subgroup G)).pCoreIn 2 at hc
  rw [D.localOrbit_eq] at hr hc
  change IsPReduced 2 (V.subgroupOf (LT E)) at hr
  change (T : Subgroup G) ⊓ centralizer (V : Set G) = (LT E).pCoreIn 2 at hc
  refine ⟨hT, hpoint, hK, ?_, ?_, hr, ?_⟩
  · simpa only [LT, Closure.Geometry.M, D.localOrbit_eq] using hu.normalizer_unique
  · have hchar : HasCharacteristicTwo (LT E) :=
      Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
        (E.input.source.simpleQTKE.evenCharacteristic T)
        ⟨E.input.source.maximal_faithful.1.1.2.2,
          fun x hx => (le_sup_right : (T : Subgroup G) ≤ LT E) hx⟩)
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar
  · rw [AmalgamLocalCores.reduced_centralizer_core _ hr]
    apply map_injective (LT E).subtype_injective
    rw [Subgroup.map_inf _ _ _ (LT E).subtype_injective,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ LT E from le_sup_right)]
    change (T : Subgroup G) ⊓ _ = (LT E).pCoreIn 2
    rw [← hc]
    apply le_antisymm
    · rintro x ⟨ht, y, hy, rfl⟩
      refine ⟨ht, fun v hv => ?_⟩
      exact congrArg Subtype.val (hy ⟨v, V_le_LT E hv⟩ hv)
    · rintro x ⟨ht, hv⟩
      refine ⟨ht, ⟨x, mem_sup_right ht⟩, ?_, rfl⟩
      intro v hv'
      exact Subtype.ext (hv v hv')

open scoped IsMulCommutative in
/-- Apply F.7 to the original chosen module after discharging its local
inputs. The criticality statement uses the literal V inside ⟨LT,KT⟩. -/
theorem exists_critical_track_of_point_geometry
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hpoint : LT E ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁ ⊔ (T : Subgroup G))
    (hK : E.K ≤ centralizer (E.V₁ : Set G)) (hout : ¬ E.K ≤ E.M)
    (hab : IsMulCommutative E.W) :
    ∃ b : ℕ, 1 < b ∧ ∃ v : Subgroup.CosetGeometry.RankTwo.Vertex (family E),
      (Subgroup.CosetGeometry.RankTwo.graph (family E)).dist
        (Subgroup.CosetGeometry.RankTwo.base (family E) false) v = b ∧
      ¬ V.subgroupOf (generated E) ≤
        Subgroup.CosetGeometry.RankTwo.ballKernel (family E) v 1 := by
  let h := localInputs_of_point_geometry E hT hpoint hK
  obtain ⟨v, hd, hc⟩ := ((sourceSetup E h hout).critical_witness
    (sourceV_ne_bot E h hout)).1
  refine ⟨distance E h hout, one_lt_distance E h hout hab, v, hd, ?_⟩
  simpa only [sourceSeed_eq] using hc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam
