module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.NormalCoreTwoClosedTransport
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Minimal parabolics through a Sylow-kernel quotient

A surjection whose kernel lies in the prescribed Sylow preserves the unique
maximal overgroup and its normal core. The proof uses the literal subgroup
correspondence; nonnormality of the Sylow descends because its full preimage
is the original Sylow. These are the quotient reductions used at the start
of Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {H A : Type*} [Group H] [Group A] [Finite H]

theorem minimalParabolic_surjective (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (f : H →* A) (hf : Function.Surjective f)
    (hk : f.ker ≤ (T : Subgroup H)) :
    IsMinimalParabolicOver (T.mapSurjective hf) ⊤ := by
  let M := minimalParabolicMax T hP
  have hM := minimalParabolicMax_spec T hP
  have hker : f.ker ≤ M := hk.trans hM.2
  have hc : IsCoatom (M.map f) := by
    refine ⟨?_,?_⟩
    · intro he
      have hh := congrArg (Subgroup.comap f) he
      rw [comap_map_eq,sup_eq_left.mpr hker,comap_top] at hh
      exact hM.1.ne_top hh
    · intro L hL
      have hlt : M < L.comap f := by
        apply lt_of_le_of_ne (map_le_iff_le_comap.mp hL.le)
        intro he
        have hh := congrArg (Subgroup.map f) he
        rw [map_comap_eq_self_of_surjective hf] at hh
        exact hL.ne hh
      have hh := congrArg (Subgroup.map f) (hM.1.2 _ hlt)
      simpa only [map_comap_eq_self_of_surjective hf,map_top_of_surjective f hf] using hh
  apply (isMinimalParabolicOver_top_iff _).mpr
  refine ⟨⟨M.map f,⟨hc,map_mono hM.2⟩,?_⟩,?_⟩
  · intro L hL
    have he := minimalParabolicMax_unique T hP
      (isCoatom_comap_of_surjective hf hL.1) (map_le_iff_le_comap.mp hL.2)
    have hh := congrArg (Subgroup.map f) he
    simpa only [map_comap_eq_self_of_surjective hf] using hh
  · intro hn
    have hnormal : ((T : Subgroup H).map f).Normal := hn
    let := hnormal
    have hh : ((T : Subgroup H).map f).comap f = (T : Subgroup H) :=
      comap_map_eq_self hk
    have hnT : (T : Subgroup H).Normal := hh ▸ (inferInstance :
      (((T : Subgroup H).map f).comap f).Normal)
    exact ((isMinimalParabolicOver_top_iff T).mp hP).2 hnT

theorem minimalParabolicMax_map (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (f : H →* A) (hf : Function.Surjective f)
    (hk : f.ker ≤ (T : Subgroup H)) :
    (minimalParabolicMax T hP).map f = minimalParabolicMax (T.mapSurjective hf)
      (minimalParabolic_surjective T hP f hf hk) := by
  let hQ := minimalParabolic_surjective T hP f hf hk
  have he := minimalParabolicMax_unique T hP
    (isCoatom_comap_of_surjective hf (minimalParabolicMax_spec _ hQ).1)
    (map_le_iff_le_comap.mp (minimalParabolicMax_spec _ hQ).2)
  have hh := congrArg (Subgroup.map f) he
  have hh' : minimalParabolicMax (T.mapSurjective hf) hQ =
      (minimalParabolicMax T hP).map f := by
    simpa only [map_comap_eq_self_of_surjective hf] using hh
  exact hh'.symm

theorem minimalParabolicCore_map (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (f : H →* A) (hf : Function.Surjective f)
    (hk : f.ker ≤ (T : Subgroup H)) :
    (minimalParabolicCore T hP).map f = minimalParabolicCore (T.mapSurjective hf)
      (minimalParabolic_surjective T hP f hf hk) := by
  let M := minimalParabolicMax T hP
  have hm : (M.map f).comap f = M := comap_map_eq_self
    (hk.trans (minimalParabolicMax_spec T hP).2)
  have hc := normalCore_comap_of_surjective f hf (M.map f)
  rw [hm] at hc
  have hh := congrArg (Subgroup.map f) hc
  rw [map_comap_eq_self_of_surjective hf] at hh
  exact hh.trans (congrArg Subgroup.normalCore (minimalParabolicMax_map T hP f hf hk))
end CFSG.Quasithin.ChapterB
