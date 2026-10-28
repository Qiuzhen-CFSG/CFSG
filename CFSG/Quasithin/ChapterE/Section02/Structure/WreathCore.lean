module
public import Theory.SpecificGroups.SymmetricFive.WreathCore
public import Theory.SpecificGroups.SymmetricFive.WreathTwoCore
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.PCoreImage

/-!
# The maximal core normalizes symmetric-five wreath components

Pull back a proper Sylow overgroup with core in the wreath base through the
literal two-core quotient. The unique minimal-parabolic maximal contains this
pullback. Its two-core lies in the prescribed Sylow and is normalized by the
pullback, hence lies in the pullback's two-core. The quotient image therefore
lies in the wreath base, which normalizes each C-component. Solvable-kernel
component lifting reflects this normalization in the original group.

Source: Aschbacher--Smith 15.2.4, printed p.1106.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
open Theory.SpecificGroups.SymmetricFive.WreathComponents
variable {H : Type*} [Group H] [Finite H]

theorem minimalParabolicMax_core_normalizes_of_symmetricFive_wreath
    (S : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (e : (H ⧸ pCore 2 H) ≃* W) {K : Subgroup H} (hK : K.IsCComponent) :
    (ChapterB.minimalParabolicMax S hP).pCoreIn 2 ≤ normalizer (K : Set H) := by
  let M := ChapterB.minimalParabolicMax S hP
  let q := QuotientGroup.mk' (pCore 2 H)
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by ext x; simp [f,q]
  have hker : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup
  obtain ⟨B,hSB,hB,hBc⟩ :=
    Theory.SpecificGroups.SymmetricFive.WreathCore.exists_sylow_overgroup_core_in_base
      (S.mapSurjective hf)
  have hpre : B.comap f ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map f) he
    rw [map_comap_eq_self_of_surjective hf,map_top_of_surjective f hf] at hh
    exact hB hh
  have hSB' : (S : Subgroup H) ≤ B.comap f := map_le_iff_le_comap.mp hSB
  have hSM : (S : Subgroup H) ≤ M := (ChapterB.minimalParabolicMax_spec S hP).2
  have hBM : B.comap f ≤ M := hP.1.le_maximal
    ⟨hSM,(ChapterB.minimalParabolicMax_spec S hP).1.covBy_top⟩ hSB'
    (lt_top_iff_ne_top.mpr hpre)
  have hNS : M.pCoreIn 2 ≤ (S : Subgroup H) := by
    have hh := pCoreIn_le_sylow M (S.subtype hSM)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSM] using hh
  have hNB : M.pCoreIn 2 ≤ (B.comap f).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) (hNS.trans hSB')
      (hBM.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  have himage : (M.pCoreIn 2).map f ≤ base := by
    have hh := map_mono (f := f) hNB
    rw [map_pCoreIn_of_ker_isPGroup f hker (B.comap f),map_comap_eq_self_of_surjective hf] at hh
    exact hh.trans hBc
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hKq : (K.map q).IsCComponent := hK.map_quotient _
  have hKw := hKq.map_equiv e
  have hn := himage.trans (base_le_component_normalizer hKw)
  rw [← map_equiv_normalizer_eq _ e] at hn
  have hnq : (M.pCoreIn 2).map q ≤ normalizer ((K.map q) : Set (H ⧸ pCore 2 H)) := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    simpa only [map_map] using hn
  have hnc := map_le_iff_le_comap.mp hnq
  rwa [normalizer_cComponent_quotient hK (pCore 2 H)] at hnc
end CFSG.Quasithin.ChapterE.Structure
