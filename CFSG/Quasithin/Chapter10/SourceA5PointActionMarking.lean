module
public import CFSG.Quasithin.Chapter10.SourceA5PointThompsonMovement
public import Theory.GroupTheory.Commutator.ConjugateSpan

/-!
# Markings in the constrained point action

In the constrained branch of Aschbacher–Smith 10.2.9, fixed-span promotion
identifies the entire orbit module as its commutator with the point component.
The centralizer bound then keeps the original smaller component nonzero and
proper in the faithful action quotient.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Fixed-span promotion keeps both the full commutator module and the
strict nonzero smaller component in the literal quotient action. -/
theorem source_a5_point_action_marking
    {v : G} (I : Subgroup G) (hLI : L ≤ I)
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ S
    let V := conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I
    let U := V.subgroupOf H
    letI := hr.normal
    ⁅V,I⁆ = V ∧ centralizer (V : Set G) ≤ D.maximalLocal ∧
      (L.subgroupOf H).map (actionMk U) ≠ ⊥ ∧
      (L.subgroupOf H).map (actionMk U) < (I.subgroupOf H).map (actionMk U) := by
  let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ S
  let W := ⁅D.fullModule,L⁆
  let V := conjugateSpanBy (W ⊓ centralizer (S : Set G)) I
  let U := V.subgroupOf H
  let := hr.normal
  have hVI : V ≤ I := conjugateSpanBy_le_self
    (inf_le_left.trans ((source_full_moved_le_component D).trans hLI))
  have hVH : V ≤ H := hVI.trans le_sup_left
  have hLH : L ≤ H := hLI.trans le_sup_left
  have hLM : L ≤ D.maximalLocal := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hCV : centralizer (V : Set G) ≤ D.maximalLocal := (centralizer_le hspan).trans hCW
  have hfull : conjugateSpanBy W I = V := le_antisymm
    (conjugateSpanBy_le hspan (le_normalizer_conjugateSpanBy _ I))
    (conjugateSpanBy_mono inf_le_left le_rfl)
  have hcomm : ⁅V,I⁆ = V := by
    rw [←hfull]
    exact (conjugateSpanBy_eq_commutator_of_seed W I I L le_rfl I.le_normalizer hLI
      (source_full_moved_eq_commutator D).symm).symm
  have hkerM : (actionMk U).ker ≤ D.maximalLocal.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro a ha
    apply hCV
    intro w hw
    exact congrArg H.subtype (ha ⟨w,hVH hw⟩ hw)
  have hnonzero : (L.subgroupOf H).map (actionMk U) ≠ ⊥ := by
    intro hz
    have hLC : L.subgroupOf H ≤ (actionMk U).ker := (Subgroup.map_eq_bot_iff _).mp hz
    have hLC' : L.subgroupOf H ≤ centralizer (U : Set H) := by
      simpa only [actionMk,QuotientGroup.ker_mk'] using hLC
    have hLW : L ≤ centralizer (W : Set G) := by
      intro l hl w hw
      exact congrArg H.subtype (hLC' (show (⟨l,hLH hl⟩ : H) ∈ L.subgroupOf H from hl) ⟨w,hVH (hspan hw)⟩ (hspan hw))
    exact source_full_moved_ne_bot D ((source_full_moved_eq_commutator D).symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hLW)))
  refine ⟨hcomm,hCV,hnonzero,lt_of_le_of_ne (map_mono (comap_mono hLI)) ?_⟩
  intro he
  have hle : I.subgroupOf H ≤ L.subgroupOf H ⊔ (actionMk U).ker := by
    rw [←comap_map_eq]
    exact map_le_iff_le_comap.mp he.ge
  have hIM : I.subgroupOf H ≤ D.maximalLocal.subgroupOf H :=
    hle.trans (sup_le (comap_mono hLM) hkerM)
  exact hout (fun i hi => hIM (show (⟨i,(show I ≤ H from le_sup_left) hi⟩ : H) ∈ I.subgroupOf H from hi))
end CFSG.Quasithin.Chapter10
