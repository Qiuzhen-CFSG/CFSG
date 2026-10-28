module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsSourceLocals
public import Stellmacher.Recognition.Parrott.LocalInputs

/-!
# The actual Parrott seed in the original Tits branch

The marked first parabolic supplies the full involution centralizer. Empty Lf
makes every two-local containing an ambient Sylow solvable. Thus the derived
core normalizer is this centralizer, and Parrott's first fusion argument
constructs the actual second elementary subgroup F. Its own normalizer is
solvable by the same source theorem.

All witnesses belong to the original ambient group and retain the original
central involution. No N₂, local-solvability or normalizer-identity premise is
added to the source statement. The later normalizer and transfer arguments
are still needed for ambient Tits recognition.

Source: Aschbacher--Smith 14.2.22, printed p.989; Parrott (1972), pp.673--675.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marked Tits branch constructs its actual second elementary
subgroup and proves solvability of its normalizer without an N₂ assumption. -/
theorem source_tits_second_elementary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel : Nonempty (Tits.ExceptionalParabolics.first ≃* H)) :
    ∃ z : G, zpowers z = centralInvolutions T ∧ Recognition.ParrottCentralizerHypotheses z ∧
      ∃ d : Recognition.ParrottSecondElementaryData z,
        Group.IsSolvable (normalizer (d.F : Set G)) ∧
        normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
          ((centralizer ({z} : Set G)).subtype.comp
            (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
          centralizer ({z} : Set G) := by
  let : IsSimpleGroup G := hG.simple
  have hns : ¬ Group.IsSolvable G := fun hs =>
    hG.nonabelian (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))
  obtain ⟨z,hz,hp,hlocal⟩ := source_tits_sylow_local_solvability
    hG T hempty hM hu hmany hcard e H hH hmodel
  have hnorm := parrott_derived_normalizer_of_sylow_local_solvability z hp hlocal
  obtain ⟨d⟩ := Recognition.parrott_second_elementary_of_derived_normalizer hns z hp hnorm
  exact ⟨z,hz,hp,d,
    parrott_second_normalizer_solvable_of_sylow_local_solvability z d hlocal,hnorm⟩

/-- The exact local inputs for the later Parrott normalizer construction are
proved under the original source marking, without a global N₂ assumption. -/
theorem source_tits_local_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel : Nonempty (Tits.ExceptionalParabolics.first ≃* H)) :
    ∃ z : G, zpowers z = centralInvolutions T ∧ Recognition.ParrottCentralizerHypotheses z ∧
      Recognition.ParrottLocalInputs z := by
  obtain ⟨z,hz,hp,hlocal⟩ := source_tits_sylow_local_solvability
    hG T hempty hM hu hmany hcard e H hH hmodel
  exact ⟨z,hz,hp,{
    derived_normalizer := parrott_derived_normalizer_of_sylow_local_solvability z hp hlocal
    second_normalizer_solvable := fun d =>
      parrott_second_normalizer_solvable_of_sylow_local_solvability z d hlocal }⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
