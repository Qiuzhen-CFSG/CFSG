module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Membership
public import Theory.GroupTheory.PerfectNormalImage
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ResidualGeneration

/-!
# Generation by the original local residuals

The point residual and either the three-space or six-space residual generate L.
Their images under the original component actor generate SL₅(2) by elementary
matrices. The Sylow group normalizes both residuals and contains O₂(L), so their
join is normal after lifting through that kernel. Perfectness of L removes the
remaining solvable quotient. Every map uses the original exterior marking.

Source: Aschbacher--Smith, 12.5.4, printed p.819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Representation.SL5ExteriorSquare
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace ExteriorMarking
variable (a : ExteriorMarking D)

/-- The image under the original component actor is the concrete parabolic residual. -/
theorem componentActor_image_Li (i : ℕ) (hi : LocalIndex i) :
    ((a.Li i).subgroupOf L).map a.componentActor =
      parabolicResidual (localFlagDimension i) := by
  apply le_antisymm
  · rintro g ⟨l, hl, rfl⟩
    rw [← a.residualActor_apply i hi ⟨l, hl⟩]
    exact (a.residualActor i hi ⟨l, hl⟩).property
  · intro g hg
    obtain ⟨l, hl⟩ := a.residualActor_surjective i hi ⟨g, hg⟩
    exact ⟨⟨l, a.Li_le_L i l.property⟩, l.property,
      (a.residualActor_apply i hi l).symm.trans (congrArg Subtype.val hl)⟩
end ExteriorMarking
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The original point residual and either relevant local residual generate L. -/
theorem point_residual_sup_local_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.marking.Li 1 ⊔ s.marking.Li i = L := by
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  let A := s.marking.Li 1 ⊔ s.marking.Li i
  have hAL : A ≤ L := sup_le (s.marking.Li_le_L 1) (s.marking.Li_le_L i)
  let B := A.subgroupOf L
  have him : B.map s.marking.componentActor = ⊤ := by
    dsimp only [B, A]
    rw [subgroupOf_sup (s.marking.Li_le_L 1) (s.marking.Li_le_L i), Subgroup.map_sup,
      s.marking.componentActor_image_Li 1 (Or.inl rfl), s.marking.componentActor_image_Li i hidx]
    exact pointResidual_sup_eq_top (localFlagDimension i)
      (by rcases hi with rfl | rfl <;> simp [localFlagDimension])
  have hcoreT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hnT : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (le_inf (s.sylow_normalizes_Li 1 (Or.inl rfl)) (s.sylow_normalizes_Li i hidx)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hncore : pCore 2 L ≤ normalizer (B : Set L) := by
    intro x hx y
    exact hnT (hcoreT (mem_map_of_mem L.subtype hx)) (y : G)
  have hgen : B ⊔ pCore 2 L = ⊤ := by
    have hh := congrArg (comap s.marking.componentActor) him
    simpa only [comap_map_eq, s.marking.componentActor_ker, comap_top] using hh
  let : B.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgen]
    exact sup_le B.le_normalizer hncore))
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let : Group.IsSolvable s.marking.componentActor.ker := by
    rw [s.marking.componentActor_ker]
    let : Group.IsNilpotent (pCore 2 L) := pCore_isNilpotent
    infer_instance
  have he := eq_top_of_perfect_of_solvable_kernel_image s.marking.componentActor B him
  have he' := congrArg (map L.subtype) he
  simpa only [B, map_subgroupOf_eq_of_le hAL, ← MonoidHom.range_eq_map, range_subtype] using he'

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
