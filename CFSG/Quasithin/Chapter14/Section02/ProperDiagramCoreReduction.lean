module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramCoreModel
/-!
# Original ambient two-core control for a marked diagram residual

The common Sylow contains O₂(M), so this core lies in H intersection M
and hence in its two-core. Transport to the H carrier applies the exact
marked action from 14.2.12. The selected symplectic residual is normalized;
a failure for the selected linear residual forces field order four.

Source: Aschbacher--Smith 14.2.12, printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem shared_sylow_twoCore_le_overlap_core
    (T : Sylow 2 G) (M H : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H) :
    M.pCoreIn 2 ≤ (T : Subgroup G) ∧
      M.pCoreIn 2 ≤ (((H ⊓ M).subgroupOf H).pCoreIn 2).map H.subtype := by
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using
      pCoreIn_le_sylow M (T.subtype hTM)
  refine ⟨hQT,?_⟩
  rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le inf_le_left]
  exact (le_inf (le_inf (hQT.trans hTH) (pCoreIn_le 2 M)) le_rfl).trans
    (inf_pCoreIn_le_of_le 2 (inf_le_right : H ⊓ M ≤ M))

theorem ambient_linear_core_normalizes_or_four
    (T : Sylow 2 G) (M H : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (K : Subgroup H) [K.Normal]
    (e : sourceImage ((H ⊓ M).subgroupOf H) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap ((H ⊓ M).subgroupOf H) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F)
    (hF : Nat.card F = 2^f) (hf : 1 < f) :
    M.pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer
      ((markedParabolicResidual ((H ⊓ M).subgroupOf H) K e
        (Matrix.PSL3.LinearThree.pointParabolic F)).map H.subtype : Set G) ∨ f = 2 := by
  by_cases hf2 : f = 2
  · exact Or.inr hf2
  left
  obtain ⟨hQT,hQ⟩ := shared_sylow_twoCore_le_overlap_core T M H hTM hTH
  refine le_inf hQT ?_
  intro g hg
  obtain ⟨x,hx,rfl⟩ := hQ hg
  have hn := (linear_core_actor_normalizes_or_four ((H ⊓ M).subgroupOf H) K e
    he hF hf x hx).resolve_right hf2
  exact (markedParabolicResidual ((H ⊓ M).subgroupOf H) K e _).le_normalizer_map
    H.subtype (mem_map_of_mem H.subtype hn)

theorem ambient_symplectic_core_normalizes
    (T : Sylow 2 G) (M H : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (K : Subgroup H) [K.Normal]
    (e : sourceImage ((H ⊓ M).subgroupOf H) K ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F)
    (he : (componentOverlap ((H ⊓ M).subgroupOf H) K).map e.toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.borel)
    (hF : Nat.card F = 2^f) (hf : 1 < f) :
    M.pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer
      ((markedParabolicResidual ((H ⊓ M).subgroupOf H) K e
        (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F))).map H.subtype : Set G) := by
  obtain ⟨hQT,hQ⟩ := shared_sylow_twoCore_le_overlap_core T M H hTM hTH
  refine le_inf hQT ?_
  intro g hg
  obtain ⟨x,hx,rfl⟩ := hQ hg
  have hn := symplectic_core_actor_normalizes ((H ⊓ M).subgroupOf H) K e he hF hf x hx
  exact (markedParabolicResidual ((H ⊓ M).subgroupOf H) K e _).le_normalizer_map
    H.subtype (mem_map_of_mem H.subtype hn)
end CFSG.Quasithin.Chapter14.Section02
