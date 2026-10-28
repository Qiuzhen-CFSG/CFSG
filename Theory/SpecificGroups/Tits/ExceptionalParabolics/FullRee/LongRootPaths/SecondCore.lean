module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.SecondCoreCertificate
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.ShortCentralizer

/-!
# The marked six-step endpoint involutions in the actual second core

All relative roots except the omitted Levi pair belong to the linear
radical. Parrott's positive word for the left endpoint uses only those
roots. Both marked endpoint involutions and their actual short-root
commutator therefore lie in the intrinsic two-core of the full second
parabolic. This retains the literal root/core inclusion, independently of
the separate geodesic attachment. Source: J.4.7, printed p.444.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Subgroup ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ReeF4.DerivedTits.Realization
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates

/-- The actual second intrinsic core included in the full group. -/
def secondCore : Subgroup (Model 0) := (pCore 2 second).map second.subtype

theorem secondCore_eq_radical : secondCore=radical 0 .linear :=
  Binary.pCore_map_seed_subtype .linear

private theorem quartet_radical (i j : Fin 4) : IsRadicalRoot .linear (quartetRoots i j) := by
  have h := ((rootBlocks (.radical .linear)).roots (.inr (i,j))).property
  change IsRadicalRoot .linear _ at h
  have he : quartetRoots i j = ((rootBlocks (.radical .linear)).roots (.inr (i,j))).val := by
    apply Subtype.ext
    change ((rootBlocks .positive).roots (.inr (i,j))).val.val = _
    rw [rootBlocks_roots_val,rootBlocks_roots_val]
    rfl
  exact he.symm ▸ h

private theorem pair_radical (i : Fin 3) (j : Fin 2) : IsRadicalRoot .linear (pairRoots i.succ j) := by
  have h := ((rootBlocks (.radical .linear)).roots (.inl (i,j))).property
  change IsRadicalRoot .linear _ at h
  have he : pairRoots i.succ j = ((rootBlocks (.radical .linear)).roots (.inl (i,j))).val := by
    apply Subtype.ext
    change ((rootBlocks .positive).roots (.inl (i.succ,j))).val.val = _
    rw [rootBlocks_roots_val,rootBlocks_roots_val]
    rfl
  exact he.symm ▸ h

private theorem quartet_mem_radical (i : Fin 4) : quartetElement i∈splitRadical 0 .linear := by
  have h (j : Fin 4) : rootGeneratorInGroup 0 (quartetRoots i j) 1∈splitRadical 0 .linear :=
    subset_closure ⟨_,1,quartet_radical i j,rfl⟩
  rw [quartetElement_eq]
  exact (splitRadical 0 .linear).mul_mem ((splitRadical 0 .linear).mul_mem (h 0) (h 1)) (h 3)

private theorem pair_mem_radical (i : Fin 3) : pairElement i.succ∈splitRadical 0 .linear := by
  have h (j : Fin 2) : rootGeneratorInGroup 0 (pairRoots i.succ j) 1∈splitRadical 0 .linear :=
    subset_closure ⟨_,1,pair_radical i j,rfl⟩
  rw [pairElement_eq]
  exact (splitRadical 0 .linear).mul_mem (h 0) (h 1)

private theorem relative_mem_radical (i : Fin 8) (hi : i≠7) :
    ReeF4.DerivedTits.Realization.u i∈splitRadical 0 .linear := by
  fin_cases i
  · exact quartet_mem_radical 0
  · exact pair_mem_radical 0
  · exact quartet_mem_radical 3
  · exact pair_mem_radical 2
  · exact quartet_mem_radical 1
  · exact pair_mem_radical 1
  · exact quartet_mem_radical 2
  · exact (hi rfl).elim

/-- The seven positive Parrott root words outside the linear Levi lie in
its actual intrinsic core. -/
theorem generator_mem_secondCore (i : ParrottGenerator)
    (hr1 : i≠.r1) (hr8 : i≠.r8) (hs8 : i≠.s8) :
    atlasEmbedding (atlas1600ParrottAssignment i)∈secondCore := by
  rw [secondCore_eq_radical]
  change toSplitGroup 0 (atlasEmbedding _)∈splitRadical 0 .linear
  rw [atlasEmbedding_generator_matrix]
  cases i with
  | r1 => exact (hr1 rfl).elim
  | r8 => exact (hr8 rfl).elim
  | s8 => exact (hs8 rfl).elim
  | s1 | s3 | s5 =>
    exact (splitRadical 0 .linear).mul_mem
      (relative_mem_radical _ (by decide)) (relative_mem_radical _ (by decide))
  | s2 | s4 | s6 => exact relative_mem_radical _ (by decide)
  | s7 =>
    exact (splitRadical 0 .linear).mul_mem
      (relative_mem_radical _ (by decide))
      ((splitRadical 0 .linear).inv_mem (relative_mem_radical _ (by decide)))

theorem u_mem_secondCore : u∈secondCore := generator_mem_secondCore .s1
  (by decide) (by decide) (by decide)

theorem leftSix_mem_secondCore : leftSix∈secondCore := by
  rw [leftSix,Atlas.leftWord_positive]
  simp only [map_mul,map_pow]
  have h (i : ParrottGenerator) (h1:i≠.r1) (h8:i≠.r8) (hS:i≠.s8) :
      atlasEmbedding (Atlas.a i)∈secondCore := generator_mem_secondCore i h1 h8 hS
  exact secondCore.mul_mem
    (secondCore.mul_mem
      (secondCore.mul_mem
        (secondCore.mul_mem
          (secondCore.mul_mem (h .s1 (by decide) (by decide) (by decide))
            (h .s3 (by decide) (by decide) (by decide)))
          (h .s4 (by decide) (by decide) (by decide)))
        (secondCore.pow_mem (h .s5 (by decide) (by decide) (by decide)) 3))
      (h .s6 (by decide) (by decide) (by decide)))
    (secondCore.pow_mem (h .s7 (by decide) (by decide) (by decide)) 2)

theorem shortCommutator_mem_secondCore : shortCommutator∈secondCore := by
  rw [← commutator_eq_short]
  exact secondCore.mul_mem (secondCore.mul_mem
    (secondCore.mul_mem leftSix_mem_secondCore u_mem_secondCore)
      (secondCore.inv_mem leftSix_mem_secondCore)) (secondCore.inv_mem u_mem_secondCore)

end Tits.ExceptionalParabolics.FullRee.LongRootPaths
