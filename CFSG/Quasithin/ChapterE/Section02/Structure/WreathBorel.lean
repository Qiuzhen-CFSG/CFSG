module
public import Theory.SpecificGroups.SymmetricFive.WreathTwoCore
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentSylowNormalizer
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.Quotient
public import Theory.GroupTheory.QuotientIntersection

/-!
# Wreath component Borels lie in the original maximal subgroup

A C-component maps to an actual A₅ component of the symmetric-five wreath
quotient. The quotient Sylow/component intersection is exactly the image
of the original intersection, because the quotient kernel lies in the
original Sylow. The component Sylow-normalizer theorem puts the image
Borel in the quotient minimal-parabolic maximal. The original maximal is
its full preimage, which proves the original Borel containment.

Source: Aschbacher--Smith B.6.8(3), E.2.3(3), and 15.2.4,
printed pp.114, 216, and 1106--1107.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
open Theory.SpecificGroups.SymmetricFive.WreathComponents
variable {H : Type*} [Group H] [Finite H]

/-- Every actual C-component Borel lies in the original maximal Sylow overgroup. -/
theorem minimalParabolicMax_borel_of_symmetricFive_wreath
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (e : (H ⧸ pCore 2 H) ≃* W) {K : Subgroup H} (hK : K.IsCComponent) :
    K ⊓ normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H) ≤
      ChapterB.minimalParabolicMax T hP := by
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' (pCore 2 H)
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by ext x; simp [f,q]
  have hker : f.ker ≤ (T : Subgroup H) := hk ▸ pCore_isPGroup.le_sylow_of_normal T
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hKq : (K.map q).IsCComponent := hK.map_quotient _
  have hKw : (K.map f).IsCComponent := by
    simpa only [map_map] using hKq.map_equiv e
  obtain ⟨a⟩ := component_equiv hKw
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (K.map f) := a.isSimpleGroup
  let : IsQuasisimple (alternatingGroup (Fin 5)) := by
    rw [← symmetric_residual]
    exact symmetric_residual_quasisimple
  have hcomp : IsComponent W (K.map f) := ⟨hKw.subnormal,IsQuasisimple.of_mulEquiv a.symm⟩
  have heven : 2 ∣ Nat.card (K.map f) := by
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hmp := ChapterB.minimalParabolic_surjective T hP f hf hker
  have hb := ChapterB.component_sylow_normalizer_le_maximal (T.mapSurjective hf) hmp hcomp heven
  have hmap : (K ⊓ normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H)).map f ≤
      (K.map f) ⊓ normalizer (((T : Subgroup H).map f ⊓ K.map f) : Set W) := by
    apply le_inf (map_mono inf_le_left)
    have hn := (map_mono (f := f) (show K ⊓ normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H) ≤
      normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H) from inf_le_right)).trans
        (((T : Subgroup H) ⊓ K).le_normalizer_map f)
    have hi : ((T : Subgroup H) ⊓ K).map f = (T : Subgroup H).map f ⊓ K.map f := by
      rw [inf_comm (T : Subgroup H) K,map_inf_of_ker_le f K T hker,inf_comm]
    rwa [hi] at hn
  have hh := hmap.trans hb
  rw [← ChapterB.minimalParabolicMax_map T hP f hf hker] at hh
  have hpre := map_le_iff_le_comap.mp hh
  rwa [comap_map_eq_self (hker.trans (ChapterB.minimalParabolicMax_spec T hP).2)] at hpre
end CFSG.Quasithin.ChapterE.Structure
