module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Intersection
public import Theory.SpecificGroups.Triality.SolvableFixedRank
public import Theory.SpecificGroups.Triality.CubicComponentAction
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Excluding the ordinary triality component in original 15.2.24

The actual triality component is O^{3′}(I). Thus the original H intersection
contains K and has three-rank two. Transport its full Sylow and the marked
inner involution along the given model isomorphism. The solvable fixed-Sylow
bound contradicts this rank, for every binary triality field parameter.
Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)

include d
/-- The original marked triality component contradicts its actual solvable Sylow intersection. -/
theorem not_triality_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hs : IsSimpleGroup c.component) {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2^n) c.component)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff c.component n hn).mp hm
  let := hs
  let : IsQuasisimple c.component := c.isComponent.2
  have hc : center c.component = ⊥ := center_eq_bot_of_simple_perfect
  let q := ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e
  have hres := (Triality.Standard.CubicComponentAction.component_eq_primeClosure_and_residual
    ((Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin 3 (by decide) (by decide))
    c.isComponent (by rw [hc]; simp) n hn q).2
  obtain ⟨Q,hQ⟩ := component_intersection_sylow d c hP
  let J := componentIntersection (H := H) c
  let J' := J.map e.toMonoidHom
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have horder := marked_component_action_order_two c (marked_centralizer d hI hz hzne).1 hz hzne a ha
  have hb : orderOf b = 2 := (MulAut.congr e).orderOf_eq a |>.trans horder
  have hbi : b ∈ (MulAut.conj (G := Triality.Standard.BinaryCarrier n hn)).range := by
    obtain ⟨x,hx⟩ := hi
    exact ⟨e x,by change MulAut.conj (e x) = MulAut.congr e a; rw [←hx,MulAut.congr_conj]⟩
  let : Group.IsSolvable J := component_intersection_solvable d c
  have hJs : Group.IsSolvable J' := Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupMap_surjective J)
  have hRJ : (R : Subgroup _) ≤ J' := map_mono hQ
  have hfix : J' ≤ b.fixedSubgroup := by
    rintro y ⟨x,hx,rfl⟩
    rw [MulAut.mem_fixedSubgroup]
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply,(MulAut.mem_fixedSubgroup _ _).mp
      (component_intersection_fixed d c hI hz hzne a ha hx)]
  have hu := Triality.Standard.solvable_sylow_fixed_three_rank_le_one n hn b hb hbi R J' hJs hRJ hfix
  have hl := component_intersection_three_rank d c hI hres
  rw [primeRank_equiv 3 (e.subgroupMap J)] at hl
  change 2 ≤ primeRank 3 J' at hl
  omega

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
