module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSelectedCoreOrbit
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightGeometry

/-!
# The original canonical family supplies the pair-core orbit bound

The source family has at most two members and is invariant under the
original T, since T normalizes both the residual and its own intersection
with the residual. Its actual conjugation orbit therefore supplies the
normalizer index bound. The same family's generation clause identifies
the core orbit without separate generation or index assumptions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G} {ℛ : Set (Subgroup G)}

private theorem family_normalizer_index
    (geom : Global.RightGeometry T L H ℛ)
    (hTH : (T : Subgroup G) ≤ H) (hR : R ∈ ℛ) :
    ((T : Subgroup G) ⊓ normalizer (R : Set G)).relIndex (T : Subgroup G) ≤ 2 := by
  let : MulAction (T : Subgroup G) (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp (T : Subgroup G).subtype)
  have hsub : MulAction.orbit (T : Subgroup G) R ⊆ ℛ := by
    rintro Q ⟨t,rfl⟩
    apply geom.invariant t (hTH.trans (le_normalizer_residual H) t.property)
      _ R hR
    exact ((le_inf (T : Subgroup G).le_normalizer
      (hTH.trans (le_normalizer_residual H))).trans inf_normalizer_le_normalizer_inf) t.property
  have hb : (MulAction.stabilizer (T : Subgroup G) R).index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard hsub).trans geom.small
  have he : MulAction.stabilizer (T : Subgroup G) R =
      ((T : Subgroup G) ⊓ normalizer (R : Set G)).subgroupOf (T : Subgroup G) := by
    ext t
    change R.map (MulAut.conj (t : G)).toMonoidHom = R ↔
      (t : G) ∈ (T : Subgroup G) ⊓ normalizer (R : Set G)
    exact ⟨fun hh => ⟨t.property,mem_normalizer_iff_map_conj_eq.mpr hh⟩,
      fun hh => mem_normalizer_iff_map_conj_eq.mp hh.2⟩
  rwa [he] at hb

/-- Every selected member of the actual source family has the same
index-two Sylow normalizer as its nonzero pair core. -/
theorem original_selected_family_core_normalizer
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (geom : Global.RightGeometry T L H ℛ) (hR : R ∈ ℛ)
    (hne : (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 ≠ ⊥) :
    let U := (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2
    (T : Subgroup G) ⊓ normalizer (U : Set G) =
      (T : Subgroup G) ⊓ normalizer (R : Set G) ∧
    ((T : Subgroup G) ⊓ normalizer (U : Set G)).relIndex (T : Subgroup G) = 2 :=
  original_selected_pair_core_normalizer d hH (geom.generates R hR)
    (family_normalizer_index geom hH.1.1.2 hR) hne

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
