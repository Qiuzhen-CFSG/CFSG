module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import Theory.GroupTheory.NormalCoreTwoClosedTransport
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Minimal parabolics through a normal-core quotient

The unique maximal subgroup and its normal core descend through every
surjection whose kernel lies in that core. If the image Sylow were normal,
it would lie in the image core; upstairs this puts the whole original Sylow
in J, and B.6.8 forces T = O₂(H), a contradiction. The kernel need not be a
two-group or lie in T. In particular this applies to the actual quotient H/J.

Source: Aschbacher–Smith E.2.2, printed pp.215–216, quotient reduction.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {H A : Type*} [Group H] [Group A] [Finite H]

theorem minimalParabolic_surjective_core (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (f : H →* A) (hf : Function.Surjective f)
    (hk : f.ker ≤ minimalParabolicCore T hP) :
    IsMinimalParabolicOver (T.mapSurjective hf) ⊤ := by
  let M := minimalParabolicMax T hP
  let J := minimalParabolicCore T hP
  have hM := minimalParabolicMax_spec T hP
  have hker : f.ker ≤ M := hk.trans (normalCore_le M)
  have hm : (M.map f).comap f = M := comap_map_eq_self hker
  let emb : Subgroup A ↪o Subgroup H :=
    ⟨⟨Subgroup.comap f,comap_injective hf⟩,comap_le_comap_of_surjective hf⟩
  have hc : IsCoatom (M.map f) := emb.isCoatom_of_map_top_of_image (comap_top f)
    (show IsCoatom ((M.map f).comap f) from hm.symm ▸ hM.1)
  have hcore : ((M.map f).normalCore).comap f = J := by
    rw [← normalCore_comap_of_surjective f hf,hm]
    rfl
  apply (isMinimalParabolicOver_top_iff _).mpr
  refine ⟨⟨M.map f,⟨hc,map_mono hM.2⟩,?_⟩,?_⟩
  · intro L hL
    have he := minimalParabolicMax_unique T hP
      (isCoatom_comap_of_surjective hf hL.1) (map_le_iff_le_comap.mp hL.2)
    have hh := congrArg (Subgroup.map f) he
    simpa only [map_comap_eq_self_of_surjective hf] using hh
  · intro hn
    let : ((T : Subgroup H).map f).Normal := hn
    have hTC : (T : Subgroup H).map f ≤ (M.map f).normalCore :=
      normal_le_normalCore.mpr (map_mono hM.2)
    have hTJ : (T : Subgroup H) ≤ J := hcore ▸ map_le_iff_le_comap.mp hTC
    have hTQ : (T : Subgroup H) = pCore 2 H := by
      calc (T : Subgroup H) = (T : Subgroup H) ⊓ J := (inf_eq_left.mpr hTJ).symm
           _ = pCore 2 H := minimalParabolic_sylow_inf_core T hP
    have hTnormal : (T : Subgroup H).Normal := by rw [hTQ];infer_instance
    exact ((isMinimalParabolicOver_top_iff T).mp hP).2 hTnormal

theorem minimalParabolicMax_map_core (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (f : H →* A) (hf : Function.Surjective f)
    (hk : f.ker ≤ minimalParabolicCore T hP) :
    (minimalParabolicMax T hP).map f = minimalParabolicMax (T.mapSurjective hf)
      (minimalParabolic_surjective_core T hP f hf hk) := by
  let hQ := minimalParabolic_surjective_core T hP f hf hk
  have he := minimalParabolicMax_unique T hP
    (isCoatom_comap_of_surjective hf (minimalParabolicMax_spec _ hQ).1)
    (map_le_iff_le_comap.mp (minimalParabolicMax_spec _ hQ).2)
  have hh := congrArg (Subgroup.map f) he
  have hh' : minimalParabolicMax (T.mapSurjective hf) hQ =
      (minimalParabolicMax T hP).map f := by
    simpa only [map_comap_eq_self_of_surjective hf] using hh
  exact hh'.symm

theorem minimalParabolicCore_map_core (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (f : H →* A) (hf : Function.Surjective f)
    (hk : f.ker ≤ minimalParabolicCore T hP) :
    (minimalParabolicCore T hP).map f = minimalParabolicCore (T.mapSurjective hf)
      (minimalParabolic_surjective_core T hP f hf hk) := by
  let M := minimalParabolicMax T hP
  have hm : (M.map f).comap f = M := comap_map_eq_self (hk.trans (normalCore_le M))
  have hc := normalCore_comap_of_surjective f hf (M.map f)
  rw [hm] at hc
  have hh := congrArg (Subgroup.map f) hc
  rw [map_comap_eq_self_of_surjective hf] at hh
  exact hh.trans (congrArg Subgroup.normalCore (minimalParabolicMax_map_core T hP f hf hk))
end CFSG.Quasithin.ChapterB
