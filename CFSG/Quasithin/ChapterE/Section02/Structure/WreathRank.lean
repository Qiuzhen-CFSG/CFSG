module
public import Theory.SpecificGroups.SymmetricFive.WreathRank
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.Quasithin.CoprimeRank

/-!
# Three-rank in the maximal subgroup of a symmetric-five wreath parabolic

A prescribed Sylow subgroup in S₅ wreath C₂ lies in a proper subgroup of
three-rank at least two. Pull this subgroup back through the original
H/O₂(H) marking. Minimal-parabolic uniqueness puts the pullback in the
original maximal subgroup. Its image therefore has three-rank at least
two, and the two-group kernel preserves that rank.

The theorem requires only the literal quotient marking and the genuine
minimal-parabolic hypothesis. It is the rank input used by the Omega
branch of Aschbacher--Smith 15.2.4, printed p.1106, following E.2.2.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

/-- The original unique maximal above the Sylow has three-rank at least two. -/
theorem minimalParabolicMax_three_rank_of_symmetricFive_wreath
    (S : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (e : (H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) :
    2 ≤ primeRank 3 (ChapterB.minimalParabolicMax S hP) := by
  let M := ChapterB.minimalParabolicMax S hP
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext x
    simp [f]
  obtain ⟨B,hSB,hB,hBr⟩ :=
    Theory.SpecificGroups.SymmetricFive.WreathRank.exists_proper_sylow_overgroup_rank_two
      (S.mapSurjective hf)
  have hpre : B.comap f ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map f) he
    rw [map_comap_eq_self_of_surjective hf,map_top_of_surjective f hf] at hh
    exact hB hh
  have hSM : (S : Subgroup H) ≤ B.comap f := map_le_iff_le_comap.mp hSB
  have hBM : B.comap f ≤ M := hP.1.le_maximal
    ⟨(ChapterB.minimalParabolicMax_spec S hP).2,
      (ChapterB.minimalParabolicMax_spec S hP).1.covBy_top⟩ hSM
    (lt_top_iff_ne_top.mpr hpre)
  have hBM' : B ≤ M.map f := by
    have hh := map_mono (f := f) hBM
    rwa [map_comap_eq_self_of_surjective hf] at hh
  have hmon := Theory.GroupTheory.primeRank_le_of_injective 3 (Subgroup.inclusion hBM')
    (Subgroup.inclusion_injective hBM')
  have hker : IsPGroup 2 (f.subgroupMap M).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  obtain ⟨k,hk⟩ := hker.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card (f.subgroupMap M).ker) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have he := primeRank_eq_of_surjective_of_coprime 3 (f.subgroupMap M)
    (f.subgroupMap_surjective M) hcop
  exact (hBr.trans hmon).trans_eq he.symm
end CFSG.Quasithin.ChapterE.Structure
