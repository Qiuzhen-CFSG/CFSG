module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Coordinates
public import Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

/-!
# The intrinsic two-core of the paired-offender parabolic

The partition stabilizer `parabolic` is the concrete four-block stabilizer in
S₈, and the sixteen words defining `blockCore` are exactly its two block
Klein-four groups. These equalities identify the embedded two-core with
`blockCore`, and the intrinsic two-core with `blockCore.subgroupOf parabolic`.
In particular, the block core is normal relative to the parabolic.

The core theorem is reused from `SymmetricEight.FourBlockCoreAction`. There,
conjugation of double transpositions proves normality of K = V₄ × V₄. The
parabolic acts irreducibly on K, so the nontrivial intersection of K with the
center of the two-core P forces K ≤ Z(P). The explicit centralizer calculation
C_S₈(K) ≤ K then gives P = K. That module adapts the private permutation
arguments of `A6ShadowTwoLocals.FourStructure`. The comparison of the two
sixteen-element descriptions below is checked by the Lean kernel.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.25, calculations (I)–(IV), printed pp.1133–1134 (PDF pp.1150–1151).
This supplies the concrete parabolic core identity used in those quotient
calculations; the parent retains the source theorem's final assembly.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterB.Offenders.Eight
open Theory.SpecificGroups.SymmetricEight

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

/-- The two definitions preserve the same unordered four-point partition. -/
theorem parabolic_eq_fourStabilizer : parabolic = A6ShadowTwoLocals.fourStabilizer := rfl

/-- The sixteen core words are precisely the two block Klein-four groups. -/
theorem blockCore_eq_kleinGroup : blockCore = FourBlockCoreAction.kleinGroup := by
  have hf : ∀ i : Fin 16, ∃ a b : Fin 4,
      coreWords i = FourBlockCoreAction.kleinPerm a b := by decide +kernel
  have hb : ∀ a b : Fin 4, ∃ i : Fin 16,
      coreWords i = FourBlockCoreAction.kleinPerm a b := by decide +kernel
  apply le_antisymm
  · rintro _ ⟨i, rfl⟩
    exact hf i
  · rintro _ ⟨a, b, rfl⟩
    exact hb a b

/-- The block core lies in the parabolic through the canonical Sylow subgroup. -/
theorem blockCore_le_parabolic : blockCore ≤ parabolic :=
  blockCore_le_sylow.trans sylow_le_parabolic

/-- The entire parabolic two-core, embedded in S₈, is the block core. -/
theorem parabolic_pCoreIn : parabolic.pCoreIn 2 = blockCore := by
  rw [parabolic_eq_fourStabilizer, blockCore_eq_kleinGroup]
  exact FourBlockCoreAction.fourStabilizer_pCoreIn

/-- The intrinsic two-core is the restriction of the block core to the parabolic. -/
theorem parabolic_pCore : pCore 2 parabolic = blockCore.subgroupOf parabolic := by
  rw [← parabolic_pCoreIn, Subgroup.pCoreIn, Subgroup.subgroupOf]
  exact (Subgroup.comap_map_eq_self_of_injective parabolic.subtype_injective _).symm

/-- Normality is inside the parabolic, with its own group structure. -/
instance blockCore_normal_in_parabolic : (blockCore.subgroupOf parabolic).Normal := by
  rw [← parabolic_pCore]
  infer_instance

/-- Every element of the parabolic normalizes the block core in S₈. -/
theorem parabolic_le_normalizer_blockCore :
    parabolic ≤ normalizer (blockCore : Set Perm) :=
  (normal_subgroupOf_iff_le_normalizer blockCore_le_parabolic).mp
    blockCore_normal_in_parabolic

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient
