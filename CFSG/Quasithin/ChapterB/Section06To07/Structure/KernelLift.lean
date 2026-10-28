module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.Quotient
-- Internal structure proof: unfold the unexposed normal-core definition.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Lifting minimal parabolicity through a Sylow-contained kernel

For a surjection whose kernel lies in a prescribed Sylow subgroup, all
Sylow overgroups contain the kernel. Subgroup correspondence therefore
lifts the unique maximal overgroup, while normality of the Sylow would
make its image normal. The source maximal subgroup and its normal core
are exactly the preimages of their quotient counterparts.

This is the converse transport to `minimalParabolic_surjective`. It is
used on the literal component automizer in the paired-component reduction
of Aschbacher–Smith E.2.17, printed p.230; compare E.2.2, pp.215–216.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {H A : Type*} [Group H] [Group A] [Finite H]

/-- Minimal parabolicity lifts through a kernel contained in the source Sylow. -/
theorem minimalParabolic_of_surjective (T : Sylow 2 H)
    (f : H →* A) (hf : Function.Surjective f) (hk : f.ker ≤ (T : Subgroup H))
    (hQ : IsMinimalParabolicOver (T.mapSurjective hf) ⊤) :
    IsMinimalParabolicOver T ⊤ := by
  let S := T.mapSurjective hf
  let M := minimalParabolicMax S hQ
  have hM := minimalParabolicMax_spec S hQ
  apply (isMinimalParabolicOver_top_iff T).mpr
  refine ⟨⟨M.comap f,⟨isCoatom_comap_of_surjective hf hM.1,
    map_le_iff_le_comap.mp hM.2⟩,?_⟩,?_⟩
  · intro L hL
    have hker : f.ker ≤ L := hk.trans hL.2
    have hm : (L.map f).comap f = L := comap_map_eq_self hker
    let emb : Subgroup A ↪o Subgroup H :=
      ⟨⟨Subgroup.comap f,comap_injective hf⟩,comap_le_comap_of_surjective hf⟩
    have hc : IsCoatom (L.map f) := emb.isCoatom_of_map_top_of_image (comap_top f)
      (show IsCoatom ((L.map f).comap f) from hm.symm ▸ hL.1)
    have he := minimalParabolicMax_unique S hQ hc (map_mono hL.2)
    exact hm.symm.trans (congrArg (Subgroup.comap f) he)
  · intro hn
    let : (T : Subgroup H).Normal := hn
    exact ((isMinimalParabolicOver_top_iff S).mp hQ).2
      (Subgroup.Normal.map inferInstance f hf)

/-- The lifted maximal subgroup is the exact preimage of the quotient maximal. -/
theorem minimalParabolicMax_comap (T : Sylow 2 H)
    (f : H →* A) (hf : Function.Surjective f) (hk : f.ker ≤ (T : Subgroup H))
    (hQ : IsMinimalParabolicOver (T.mapSurjective hf) ⊤) :
    minimalParabolicMax T (minimalParabolic_of_surjective T f hf hk hQ) =
      (minimalParabolicMax (T.mapSurjective hf) hQ).comap f := by
  symm
  apply minimalParabolicMax_unique
  · exact isCoatom_comap_of_surjective hf (minimalParabolicMax_spec _ hQ).1
  · exact map_le_iff_le_comap.mp (minimalParabolicMax_spec _ hQ).2

/-- The lifted normal core is the exact preimage of the quotient normal core. -/
theorem minimalParabolicCore_comap (T : Sylow 2 H)
    (f : H →* A) (hf : Function.Surjective f) (hk : f.ker ≤ (T : Subgroup H))
    (hQ : IsMinimalParabolicOver (T.mapSurjective hf) ⊤) :
    minimalParabolicCore T (minimalParabolic_of_surjective T f hf hk hQ) =
      (minimalParabolicCore (T.mapSurjective hf) hQ).comap f := by
  change (minimalParabolicMax T _).normalCore = _
  rw [minimalParabolicMax_comap T f hf hk hQ]
  exact normalCore_comap_of_surjective f hf _
end CFSG.Quasithin.ChapterB
