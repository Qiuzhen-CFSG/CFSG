module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.OmegaOrbitMoved
public import Theory.GroupTheory.ReducedNormal.Defs
public import CFSG.Quasithin.ChapterB.InternalThompsonAction
public import Theory.Representation.NormalElementaryQuotient.FullyMoved
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.SocleInduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction

/-!
# Full movement on the literal tensor overgroup action

A fully moved seed containing the Sylow omega center generates the omega
orbit under the normal component. Identity conjugation coordinates transfer
this equality to the exact action quotient and then to its offender actor.
The original tensor plane supplies the seed in source 9.3.7.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open Representation Representation.BinaryOffender
variable {H : Type*} [Group H]

theorem source_tensor_omegaOrbit_action_fully_moved
    (R V L K : Subgroup H) [K.Normal]
    (hRV : omegaCenterIn R ≤ V) (hVW : V ≤ omegaOrbit R)
    (hLK : L ≤ K) (hVL : ⁅V,L⁆ = V)
    (hr : IsPReduced 2 (omegaOrbit R)) :
    let W := omegaOrbit R
    letI := hr.normal; letI := hr.elementary
    moved (action W) (K.map (actionMk W)) = ⊤ := by
  let W := omegaOrbit R
  let := hr.normal
  let := hr.elementary
  obtain ⟨hWK,hcomm⟩ := omegaOrbit_fully_moved_of_moved_seed R V L K hRV hVW hLK hVL
  dsimp only
  rw [←SourceCompletion.coinvariants_eq_moved]
  exact Representation.NormalElementaryQuotient.coinvariants_image_eq_top W (actionMk W)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K hWK hcomm

theorem source_tensor_omegaOrbit_offender_action_fully_moved
    (R V L K : Subgroup H) [K.Normal]
    (hRV : omegaCenterIn R ≤ V) (hVW : V ≤ omegaOrbit R)
    (hLK : L ≤ K) (hVL : ⁅V,L⁆ = V)
    (hr : IsPReduced 2 (omegaOrbit R))
    (hAN : letI := hr.normal; letI := hr.elementary
      K.map (actionMk (omegaOrbit R)) ≤ offenderSubgroup (action (omegaOrbit R))) :
    let W := omegaOrbit R
    letI := hr.normal; letI := hr.elementary
    let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
    let N := offenderSubgroup ρ
    moved (ρ.comp N.subtype) ((K.map (actionMk W)).subgroupOf N) = ⊤ := by
  let := hr.normal
  let := hr.elementary
  dsimp only
  rw [moved_comp_map,map_subgroupOf_eq_of_le hAN]
  exact source_tensor_omegaOrbit_action_fully_moved R V L K hRV hVW hLK hVL hr

end CFSG.Quasithin.Chapter10

