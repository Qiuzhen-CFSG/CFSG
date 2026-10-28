module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAxisExclusion

/-!
# The original outer closure automizer is the full elementary eight-group

The marked vector-stabilizer alternatives reduce the outer branch to
the central two-group or the full elementary eight-group. The genuine
common-axis exclusion removes the first alternative. The result retains
the original induced automizer, rather than introducing a model image.

Source: Aschbacher--Smith12.7.18, printed p.845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix DuadCalculation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine outer branch induces exactly the elementary eight-group
on the original chosen six-dimensional module. -/
theorem original_tripleSix_central_closure_outer_eight
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))
    Nat.card (inducedAutomizer U W) = 8 ∧ IsElementaryAbelian 2 (inducedAutomizer U W) := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))
  obtain ⟨_,f,hf,_,hK,_,hfix,_,_,e,_,_,heven,hcases,_⟩ :=
    original_tripleSix_central_closure_automizer_cases h structural D a z hz hzT hnot
  let v := (tripleSixPointCoordinates D a z).toAdd
  let N := (inducedAutomizer U W).map f
  let B := N.subgroupOf (Hexacode.fullVectorStabilizer v)
  let β := B.map e.toMonoidHom
  have houtermodel : β = centralFactor ∨ β = productCore := by
    rcases hcases with hklein | hh
    · exfalso
      apply houter
      intro b hb
      have hfb : f b ∈ N := mem_map_of_mem _ hb
      let bS : Hexacode.fullVectorStabilizer v := ⟨f b,hfix hfb⟩
      have hmark : e bS ∈ (⊥ : Subgroup Two).prod core := by
        rw [←hklein]
        exact mem_map_of_mem _ hfb
      have hsign : hexSign (f b) = 1 := by
        apply (heven bS).mpr
        have hh := ((core_mem_iff (e bS).2).mp hmark.2).1
        rw [mem_bot.mp hmark.1]
        change 1 = if (e bS).2.sign = 1 then 1 else Equiv.swap 0 1
        rw [if_pos hh]
      have hm : f b ∈ (inducedAutomizer U K).map f := hK.symm ▸ hsign
      obtain ⟨c,hc,hcb⟩ := hm
      exact hf hcb ▸ hc
    · exact hh.2
  let E : inducedAutomizer U W ≃* β :=
    ((inducedAutomizer U W).equivMapOfInjective f hf).trans
      ((subgroupOfEquivOfLe hfix).symm.trans (B.equivMapOfInjective e.toMonoidHom e.injective))
  have hprod : β = productCore := by
    rcases houtermodel with hc | hp
    · exfalso
      apply original_tripleSix_central_closure_automizer_not_two h structural D a z hz hzT hnot houter
      exact (Nat.card_congr E.toEquiv).trans (hc ▸ centralFactor_card)
    · exact hp
  let F : inducedAutomizer U W ≃* productCore := E.trans (MulEquiv.subgroupCongr hprod)
  exact ⟨(Nat.card_congr F.toEquiv).trans productCore_card,
    IsElementaryAbelian.of_injective F.toMonoidHom F.injective⟩

end CFSG.Quasithin.Chapter12.Section07
