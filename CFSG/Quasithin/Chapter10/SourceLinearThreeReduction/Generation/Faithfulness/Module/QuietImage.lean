module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.QuietDisplacement

/-!
# Testing quiet displacement invariance on the literal full-module action

Conjugation on V_M has kernel C_M(V_M). Normalization of an odd actor's
image by the original Sylow image therefore normalizes its displacement
upstairs. The quiet fixed-space argument then kills the actor's action.
Only image normalization is needed; the actor itself need not be normal
in its product with T, and no quotient of V_M is substituted for V_M.

Source application: Aschbacher--Smith 10.2.3(2), printed p.745, using the
coprime-action step of 4.4.14, printed pp.624--625.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Literal conjugation on the full module, retaining the original actor M. -/
def sourceFullModuleConjugation : D.maximalLocal →* MulAut D.fullModule :=
  D.fullModule.normalizerMonoidHom.comp (inclusion D.maximalLocal_normalizes_fullModule)

theorem sourceFullModuleConjugation_apply (m : D.maximalLocal) (v : D.fullModule) :
    (sourceFullModuleConjugation D m v : G) = (m : G) * (v : G) * (m : G)⁻¹ := rfl

/-- The action kernel is the actual full-module centralizer inside M. -/
theorem sourceFullModuleConjugation_ker :
    (sourceFullModuleConjugation D).ker =
      (centralizer (D.fullModule : Set G)).subgroupOf D.maximalLocal := by
  ext m
  change inclusion D.maximalLocal_normalizes_fullModule m ∈
    D.fullModule.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

/-- Normalization of the literal action image gives invariance of the
original displacement subgroup, with both subtype maps retained. -/
theorem source_full_displacement_normalized_of_image
    (A : Subgroup G) (hAM : A ≤ D.maximalLocal)
    (hi : ((T : Subgroup G).subgroupOf D.maximalLocal).map
        (sourceFullModuleConjugation D) ≤
      normalizer ((A.subgroupOf D.maximalLocal).map
        (sourceFullModuleConjugation D) : Set (MulAut D.fullModule))) :
    (T : Subgroup G) ≤ normalizer (⁅D.fullModule,A⁆ : Subgroup G) := by
  let M := D.maximalLocal
  let V := D.fullModule.subgroupOf M
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hk : (sourceFullModuleConjugation D).ker ≤ centralizer (V : Set M) := by
    rw [sourceFullModuleConjugation_ker]
    intro m hm v hv
    exact Subtype.ext (hm v hv)
  have hTV : (T : Subgroup G).subgroupOf M ≤ normalizer (V : Set M) := by
    let : V.Normal := normal_subgroupOf_of_le_normalizer D.maximalLocal_normalizes_fullModule
    exact le_normalizer_of_normal
  have hn := normalizes_commutator_of_normalizes_image V (A.subgroupOf M)
    ((T : Subgroup G).subgroupOf M) (sourceFullModuleConjugation D) hk hTV hi
  have hm := (map_mono (f := M.subtype) hn).trans
    (le_normalizer_map M.subtype)
  have hA : (A.subgroupOf M).map M.subtype = A := map_subgroupOf_eq_of_le hAM
  simpa only [V,map_commutator,map_subgroupOf_eq_of_le hVM,
    hA,map_subgroupOf_eq_of_le hTM] using hm

/-- The original quiet Hall kernel fixes the full module if its actual
action image is normalized by the Sylow image. -/
theorem source_quiet_hall_kernel_fixes_of_image_normalized
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hi : ((T : Subgroup G).subgroupOf D.maximalLocal).map
        (sourceFullModuleConjugation D) ≤
      normalizer (((B.map H.subtype ⊓ sectionCentralizer (localOrbit T L)).subgroupOf
        D.maximalLocal).map (sourceFullModuleConjugation D) : Set (MulAut D.fullModule))) :
    B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G) := by
  apply (source_quiet_hall_kernel_fixes_iff_displacement_normalized D hJ hH B hBM hB).mpr
  exact source_full_displacement_normalized_of_image D _
    (inf_le_right.trans ((le_sectionCentralizer_iff _ _).mp le_rfl).1) hi

end CFSG.Quasithin.Chapter10
