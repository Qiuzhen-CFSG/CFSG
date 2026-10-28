module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.ParabolicResidual
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.PointResidual
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterQuotientParabolic

/-!
# The actual cubic actor in the original positive-center branch

Take Y=O²(C_H(v₂)) for the original H-star subgroup. The same marked
orthogonal action supplies its cubic image and movement of v₁. Original
minimal-parabolic structure and the proved three-free Baumann overlap give
Y∩M≤O₂(H), while the reduced module makes O₂(H) fix v₁. The prescribed
Sylow centralizer normalizes this literal Y by characteristicity.

The two vector stabilizer identities are the exact marking input from the
preceding orthogonal action. No component or classification conclusion is
assumed. Source: Aschbacher–Smith10.2.1, printed p.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_fixed_center_pointResidual_inf_maximal_le_core
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G):Set G)≤D.maximalLocal)
    {H : Subgroup G} (hH : H∈Chapter3.HStar (T:Subgroup G) D.maximalLocal)
    (hHN : H≤normalizer (ChapterB.baumann (T:Subgroup G):Set G))
    (f : H →* BinaryFourPlus.Wreath) (hf : Function.Surjective f) (v₂ : G) :
    pointResidual H v₂ ⊓ D.maximalLocal ≤ H.pCoreIn 2 := by
  let Y := pointResidual H v₂
  have hYH : Y≤H := (pointResidual_le H v₂).trans inf_le_left
  have hp : IsPPerfect 2 (Y.subgroupOf H) :=
    (pointResidual_twoPerfect H v₂).of_surjective
      (subgroupOfEquivOfLe hYH).symm.toMonoidHom (subgroupOfEquivOfLe hYH).symm.surjective
  have hM : Nat.Coprime 3 (Nat.card (D.maximalLocal.subgroupOf H)) := by
    simpa only [map_id] using source_a5_HStar_maximal_image_three_free D e hn hout
      hHN (MonoidHom.id H)
  have hh := parabolic_wreath_twoPerfect_inf_threeFree_le_core
    (T.subtype hH.1.1.2) (source_a5_HStar_minimal_parabolic D e hn H hH)
    f hf (Y.subgroupOf H) (D.maximalLocal.subgroupOf H) hp hM
  intro y hy
  exact mem_map_of_mem H.subtype (hh (show (⟨y,hYH hy.1⟩:H)∈
    Y.subgroupOf H ⊓ D.maximalLocal.subgroupOf H from hy))

theorem source_fixed_center_pointResidual_data
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G):Set G)≤D.maximalLocal)
    {H : Subgroup G} (hH : H∈Chapter3.HStar (T:Subgroup G) D.maximalLocal)
    (hHN : H≤normalizer (ChapterB.baumann (T:Subgroup G):Set G))
    (f : H →* BinaryFourPlus.Wreath) (hf : Function.Surjective f)
    (v₁ v₂ : G) (a b : BinaryFourPlus.Plane) (ha : a≠0) (hb : b≠0)
    (hfix₁ : ∀h:H,(BinaryFourPlus.wreathToIsometry (f h)).val (a,0)=(a,0) ↔
      (h:G)∈centralizer ({v₁}:Set G))
    (hfix₂ : ∀h:H,(BinaryFourPlus.wreathToIsometry (f h)).val (0,b)=(0,b) ↔
      (h:G)∈centralizer ({v₂}:Set G)) :
    let Y := pointResidual H v₂
    IsPPerfect 2 Y ∧ Y≤centralizer ({v₂}:Set G) ∧
      (T:Subgroup G)⊓centralizer ({v₂}:Set G)≤normalizer (Y:Set G) ∧
      Y⊓D.maximalLocal≤H.pCoreIn 2 ∧
      Nat.card ((Y.subgroupOf H).map f)=3 ∧
      ¬ Y≤centralizer ({v₁}:Set G) := by
  obtain ⟨hc,hm⟩ := pointResidual_image_and_movement H f hf v₁ v₂ a b ha hb hfix₁ hfix₂
  exact ⟨pointResidual_twoPerfect H v₂,(pointResidual_le H v₂).trans inf_le_right,
    (inf_le_inf_right _ hH.1.1.2).trans (pointResidual_normalized H v₂),
    source_fixed_center_pointResidual_inf_maximal_le_core D e hn hout hH hHN f hf v₂,hc,hm⟩

omit [Finite G] in
/-- The original reduced module makes its marked vector fixed by O₂(H). -/
theorem reduced_module_core_centralizes_vector
    (H W : Subgroup G) (hWH : W≤H) (hred : IsPReduced 2 (W.subgroupOf H))
    {v : G} (hv : v∈W) : H.pCoreIn 2≤centralizer ({v}:Set G) := by
  rintro x ⟨y,hy,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh := hred.le_centralizer_pCore (show (⟨v,hWH hv⟩:H)∈W.subgroupOf H from hv) y hy
  exact congrArg H.subtype hh

end CFSG.Quasithin.Chapter10
