module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.SevenNaturalLowerBound
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# Both ratios of the six-dimensional natural A₇ module

The even part of the three-disjoint-swap group has rank two. Its action is
quadratic because each permutation orbit has size at most two. Containment
in the full swap group bounds its fixed codimension by three; the previously
proved lower bound gives equality. This actor attains 3/2 in both infima.
The final theorem applies the calculation to the original source action
through the given group and module intertwiners.

Source: Aschbacher–Smith, K.1, printed p.452, and the A₇ row of Table B.4.5.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped ENNReal

namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource ChapterB.Offenders
open AlternatingSevenConjugatePair.ElementaryGeometry

/-- The even subgroup of the three-pair group, inside the actual A₇ carrier. -/
def sevenNaturalActor : Subgroup (alternatingGroup (Fin 7)) :=
  (pairElementary ⊓ alternatingGroup (Fin 7)).subgroupOf (alternatingGroup (Fin 7))

private theorem actor_map : sevenNaturalActor.map (alternatingGroup (Fin 7)).subtype =
    pairElementary ⊓ alternatingGroup (Fin 7) :=
  Subgroup.map_subgroupOf_eq_of_le inf_le_right

private theorem actor_card : Nat.card sevenNaturalActor = 4 := by
  unfold sevenNaturalActor
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show pairElementary ⊓ alternatingGroup (Fin 7) ≤ alternatingGroup (Fin 7)
      from inf_le_right)).toEquiv]
  exact pairElementary_even_card

/-- The actor in the source ratio calculation is a genuine nontrivial four-group. -/
theorem sevenNaturalActor_elementary : IsElementaryTwo sevenNaturalActor := by
  have hE : IsElementaryTwo (pairElementary ⊓ alternatingGroup (Fin 7)) :=
    pairElementary_isElementaryTwo.of_le inf_le_left (by
      intro h
      have hc := pairElementary_even_card
      rw [h] at hc
      simp at hc)
  let := hE.2
  refine ⟨?_, IsElementaryAbelian.subgroupOf inf_le_right⟩
  intro h
  have hc := actor_card
  rw [h] at hc
  simp at hc

theorem sevenNaturalActor_rank : rank sevenNaturalActor = 2 := by
  rw [rank, actor_card]
  decide

private theorem pair_le_D : pairElementary ≤ D 7 := by
  rw [pairElementary_eq_closure]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl | rfl
  · exact pairSwap_mem (n := 7) (m := 3) 0 (by decide)
  · exact pairSwap_mem (n := 7) (m := 3) 1 (by decide)
  · exact pairSwap_mem (n := 7) (m := 3) 2 (by decide)

private theorem full_pair_quadratic : IsQuadratic (representation (Fin 7)) pairElementary := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ v
  funext i
  change v ((firstWord b).symm ((firstWord a).symm i)) - v ((firstWord a).symm i) =
    v ((firstWord b).symm i) - v i
  have h := (by decide : ∀ (a b : Triple) (i : Fin 7),
    (firstWord a).symm i = i ∨
    ((firstWord b).symm ((firstWord a).symm i) = (firstWord a).symm i ∧
      (firstWord b).symm i = i) ∨
    ((firstWord b).symm ((firstWord a).symm i) = i ∧
      (firstWord a).symm i = (firstWord b).symm i)) a b i
  rcases h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h]
  · rw [h₁, h₂, sub_self, sub_self]
  · rw [h₁, h₂]
    exact (by decide : ∀ x y : ZMod 2, x - y = y - x) _ _

private theorem natural_pair_quadratic :
    IsQuadratic (naturalRepresentation (Fin 7)) pairElementary := by
  have hc : IsQuadratic (coreRepresentation (Fin 7)) pairElementary := by
    intro a ha b hb v
    exact Subtype.ext (full_pair_quadratic a ha b hb v)
  let e := coreEquivNatural (Fin 7) (by decide)
  exact quadratic_of_equivariant_surjection (coreRepresentation (Fin 7))
    (naturalRepresentation (Fin 7)) e.toLinearMap e.surjective
    (coreEquivNatural_equivariant (Fin 7) (by decide)) pairElementary hc

/-- The rank-two actor is quadratic on the actual deleted permutation section. -/
theorem sevenNaturalActor_quadratic : IsQuadratic (alternatingNatural 7) sevenNaturalActor := by
  intro a ha b hb v
  exact natural_pair_quadratic a.val ha.1 b.val hb.1 v

/-- Its fixed codimension is exactly three. -/
theorem sevenNaturalActor_fixedCodim : fixedCodim (alternatingNatural 7) sevenNaturalActor = 3 := by
  have he : fixedCodim (alternatingNatural 7) sevenNaturalActor =
      fixedCodim (naturalRepresentation (Fin 7))
        (pairElementary ⊓ alternatingGroup (Fin 7)) := by
    unfold fixedCodim
    rw [alternatingNatural, fixedSpace_comp_map, actor_map]
  have hle : pairElementary ⊓ alternatingGroup (Fin 7) ≤ D 7 :=
    inf_le_left.trans pair_le_D
  have hf := Submodule.finrank_mono
    (fixedSpace_antitone (naturalRepresentation (Fin 7)) hle)
  have hE := fixedCodim_add_finrank (naturalRepresentation (Fin 7))
    (pairElementary ⊓ alternatingGroup (Fin 7))
  have hD := fixedCodim_add_finrank (naturalRepresentation (Fin 7)) (D 7)
  have hDc : fixedCodim (naturalRepresentation (Fin 7)) (D 7) = 3 := by
    rw [fixedCodim_natural_eq_full_odd (Fin 7) (by decide)]
    exact ChapterB.Offenders.Odd.fixedCodim_full_disjointTranspositions (Or.inr rfl) (by decide)
  have hl := sevenNatural_actionRatio_lower sevenNaturalActor sevenNaturalActor_elementary
  rw [actionRatio, sevenNaturalActor_rank] at hl
  have hlo : 3 ≤ fixedCodim (alternatingNatural 7) sevenNaturalActor := by
    norm_num only [Nat.cast_ofNat] at hl
    rw [ENNReal.div_le_iff (by norm_num) (by simp),
      ENNReal.div_mul_cancel (by norm_num) (by simp)] at hl
    exact_mod_cast hl
  omega

/-- A single quadratic actor attains the common candidate ratio 3/2. -/
theorem sevenNaturalActor_ratio : actionRatio (alternatingNatural 7) sevenNaturalActor = 3 / 2 := by
  rw [actionRatio, sevenNaturalActor_fixedCodim, sevenNaturalActor_rank]
  norm_num

/-- The complete natural-A₇ row, with cubic and quadratic ratios separately proved. -/
theorem sevenNatural_ratios :
    quadraticRatio (alternatingNatural 7) = 3 / 2 ∧
      cubicRatio (alternatingNatural 7) = 3 / 2 := by
  have hq : quadraticRatio (alternatingNatural 7) ≤ 3 / 2 :=
    iInf_le_of_le sevenNaturalActor
      (iInf_le_of_le ⟨sevenNaturalActor_elementary, sevenNaturalActor_quadratic⟩
        sevenNaturalActor_ratio.le)
  exact ⟨le_antisymm hq sevenNatural_quadraticRatio_lower,
    le_antisymm ((cubicRatio_le_quadraticRatio _).trans hq) sevenNatural_cubicRatio_lower⟩

/-- K.1's natural-A₇ conclusion on the original module, with all ratio premises discharged. -/
theorem sevenNatural_conclusion {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    {L : Subgroup G} (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7)) : Conclusion ρ L :=
  sevenNatural_of_model_ratios hL e sevenNatural_ratios.1 sevenNatural_ratios.2

end CFSG.Quasithin.ChapterK.Alternating
