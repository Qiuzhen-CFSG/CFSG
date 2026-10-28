module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Coordinates
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Inputs
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus
public import Theory.GroupTheory.PairedElementaryEightFixedPoints

/-!
# The original linear-three pair excludes constant fixed subgroups

The survivor's actual natural action gives two elementary factors of order
eight. The original maximal local group permutes them. A rank-four elementary
actor with faithful action on their product therefore satisfies the general
paired-eight fixed-subgroup obstruction. This proves the final action
calculation in 10.3.2 without assuming an abstract automizer family or its rank.

Source: Aschbacher--Smith 10.3.2, printed p.756, final sentence of the proof.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
open Chapter3.Section02 ChapterE Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The concrete pair-action input holds for the original full module. -/
theorem pairFixedSpace : PairFixedSpaceAt T := by
  intro L D s hz A hAM hA hrank hfaith
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  let U := ⁅D.fullModule,L⁆
  let W := U.map (MulAut.conj s.exchange).toMonoidHom
  let : IsElementaryAbelian 2 U := offender_elementary_of_le (survivor_moved_le s)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hcard : Nat.card A = 16 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hn4 : n = 4 := by
      simpa only [rank,hn,Nat.log_pow (by decide : 1 < 2)] using hrank
    rw [hn,hn4]
    norm_num
  have hU : Nat.card U = 8 := moved_card s hz
  have hW : Nat.card W = 8 :=
    (card_map_of_injective (MulAut.conj s.exchange).injective).trans hU
  have hgen : D.fullModule = U ⊔ W := s.generated
  by_contra! hfixed
  apply not_uniform_fixed_pair_eight A U W hcard hU hW (survivor_pair_disjoint s hz)
    (fun a ha => survivor_moved_pair s a (hAM ha))
    (fun a ha => partner_pair s a (hAM ha))
  · rwa [← hgen]
  · intro a ha hane
    rw [← hgen]
    exact hfixed a ha hane

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
