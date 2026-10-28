module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstParabolicAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstParabolicCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenSimpleAction

/-!
# The literal action-core preimage on the first residual parabolic: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/FirstParabolicAction` proof for the local step.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Conjugation by the actual residual parabolic on the original chosen V. -/
def firstParabolicAction_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : G) :
    (firstCentralizerResidual L z ⊔ (T : Subgroup G) : Subgroup G) →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion
    ((sup_le ((firstCentralizerResidual_le L z).trans inf_le_left |>.trans L.le_normalizer)
      D.sylow_normalizes_component).trans (normalizer_component_le_module_at h structural D m)))

/-- The literal preimage in T of the two-core of the first-parabolic action image. -/
def firstActionCore_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : G) : Subgroup G :=
  ((pCore 2 (firstParabolicAction_at h structural D m z).range).comap
    ((firstParabolicAction_at h structural D m z).rangeRestrict.comp
      (inclusion (show (T : Subgroup G) ≤ firstCentralizerResidual L z ⊔ (T : Subgroup G)
        from le_sup_right)))).map (T : Subgroup G).subtype

/-- Core lifting identifies the literal action preimage in the ordinary row. -/
theorem firstActionCore_eq_firstParabolicCore_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) :
    firstActionCore_at h structural D m z = firstParabolicCore T L z := by
  let P := firstCentralizerResidual L z ⊔ (T : Subgroup G)
  let X := L ⊔ (T : Subgroup G)
  let f := firstParabolicAction_at h structural D m z
  have hPX : P ≤ X := sup_le_sup_right ((firstCentralizerResidual_le L z).trans inf_le_left) _
  have hk : f.ker = (centralizer (V : Set G)).subgroupOf P := by
    ext a
    change (inclusion _ a) ∈ V.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    apply ((local_module_centralizer_isTwo_of_ordinary D e).comap_subtype).to_le
    intro a ha
    exact ⟨hPX a.property,ha⟩
  have hpr : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hp
  have he := f.rangeRestrict.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective hpr
  have hRT := (firstParabolicCore_local_data (L := L) hz).1
  change ((pCore 2 f.range).comap (f.rangeRestrict.comp (inclusion
    (show (T : Subgroup G) ≤ P from le_sup_right)))).map (T : Subgroup G).subtype = P.pCoreIn 2
  apply le_antisymm
  · rintro x ⟨t,ht,rfl⟩
    exact ⟨inclusion le_sup_right t,he.le ht,rfl⟩
  · rintro x ⟨a,ha,rfl⟩
    refine ⟨⟨a,hRT (mem_map_of_mem P.subtype ha)⟩,?_,rfl⟩
    exact he.ge ha

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
