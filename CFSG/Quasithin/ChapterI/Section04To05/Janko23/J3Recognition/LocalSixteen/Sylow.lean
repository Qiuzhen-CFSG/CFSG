module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.Normalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.Planes

/-!
# Ambient Sylow placement in the one-class branch

The root normalizer has order 1152, so its Sylow two-subgroups have order
128. The one-class H-type centralizer gives the same order for ambient
Sylow two-subgroups. Thus a Sylow subgroup of the root normalizer containing
R is already ambient Sylow. This retains the actual subgroup inclusions
needed for the remaining fusion step of 46.14.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14, pp.257–258.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
namespace ReturningPair

/-- In the one-class case a Sylow subgroup of the literal root normalizer
is an ambient Sylow subgroup, of order 128, containing R. -/
theorem exists_ambient_sylow (P : ReturningPair D) (hc : OneInvolutionClass G) :
    ∃ S : Sylow 2 G, P.R ≤ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ normalizer (P.R : Set G) ∧ Nat.card S = 128 := by
  let N := normalizer (P.R : Set G)
  let Q := P.R.subgroupOf N
  have hQp : IsPGroup 2 Q := P.R_isPGroup.comap_subtype
  obtain ⟨S,hQS⟩ := hQp.exists_le_sylow
  have hScard : Nat.card S = 128 := by
    rw [S.card_eq_multiplicity, Geometry.Normalizer.normalizer_R_card P]
    decide +kernel
  let B := (S : Subgroup N).map N.subtype
  have hBcard : Nat.card B = 128 := by
    rw [card_map_of_injective N.subtype_injective]
    exact hScard
  obtain ⟨T,hBT⟩ := (S.isPGroup'.map N.subtype).exists_le_sylow
  have hTcard := D.localType.sylow_card_of_one_class hc T
  have hB : B = (T : Subgroup G) := eq_of_le_of_card_ge hBT (by rw [hBcard,hTcard])
  refine ⟨T,?_,?_,hTcard⟩
  · rw [←hB, ←map_subgroupOf_eq_of_le (le_normalizer : P.R ≤ N)]
    exact map_mono hQS
  · rw [←hB]
    exact map_subtype_le _
end ReturningPair
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
