module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.PSL3FourExclusion
public import Theory.Representation.BinaryOffender.QuadraticConstituentStability
public import Theory.Representation.NormalSimpleConstituent
public import Theory.Representation.BinaryOffender.ConstituentRatio
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting
public import Theory.Representation.PSL3Four.SmallDegree
public import Theory.SpecificGroups.PSL3Four.OuterTwoRank
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient

/-!
# Excluding a PSL₃(4) normal subgroup on an irreducible chief action

A faithful irreducible binary action restricts to a faithful simple
constituent of its normal PSL₃(4) subgroup. Such a constituent has dimension
at least nine. If a quadratic actor moves it, quadraticity makes the actor's
intersection with PSL₃(4) trivial. The outer two-rank bound then gives actor
rank at most two, contradicting the dimension and fixed-codimension bounds.
Thus the actor preserves the constituent.

The literal constituent stabilizer retains SQTK, has generalized Fitting
subgroup PSL₃(4), and acts faithfully on the constituent. Its quadratic
bound contradicts the proved irreducible PSL₃(4) source exclusion. Whole
actor irreducibility therefore suffices; no irreducibility of the original
normal-subgroup restriction is assumed.

Source: Aschbacher–Smith B.4.2–5 and D.3.6–9, applied in the original tensor
argument 9.2.7, printed pp.731–732.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.PSL3FourExclusion
universe u v
variable {G : Type u} [Group G] [Finite G]
 {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
 {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}} {L : Subgroup G} [L.Normal]

private theorem not_quadratic_actor_preserving_simple
 (hsq : IsSQTK K G) (hm : ClassicalGroup.IsPSL L 3 4)
 (hquot : IsPGroup 2 (G ⧸ L)) (hc : centralizer (L : Set G) = ⊥)
 (J : Subrepresentation (ρ.comp L.subtype)) (hfJ : Function.Injective J.toRepresentation)
 (hiJ : J.toRepresentation.IsIrreducible)
 (A : Subgroup G) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
 (hd : fixedCodim ρ A ≤ 2 * rank A)
 (hstable : ∀ a ∈ A, J.toSubmodule.map (ρ a) = J.toSubmodule) : False := by
 let H := subspaceStabilizer ρ J.toSubmodule
 let σ := stabilizerRepresentation ρ J.toSubmodule
 have hL : L ≤ H := le_constituent_stabilizer ρ L J
 have hAH : A ≤ H := by
   intro a ha
   exact (subspace_map_eq_iff ρ J.toSubmodule a).mp (hstable a ha)
 have hsmall : quadraticRatio σ ≤ 2 := quadraticRatio_stabilizer_le_two ρ J.toSubmodule A hA hq hd hAH
 obtain ⟨hqs,_,_⟩ := model_facts hm
 let : IsQuasisimple L := hqs
 have hfit := constituent_stabilizer_generalizedFitting_eq ρ L J hfJ hc hquot hiJ
 have hf := stabilizerRepresentation_injective_of_faithful_normal_constituent ρ L J hfJ hc
 have hi := stabilizerRepresentation_constituent_restriction_irreducible ρ L J hiJ
 obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
 have hmod : ClassicalGroup.IsPSL (L.subgroupOf H) 3 4 :=
   ⟨F,inferInstance,inferInstance,hF,⟨(subgroupOfEquivOfLe hL).trans e⟩⟩
 exact not_le_of_gt (quadraticRatio_gt_two (hsq.subgroup H) hfit hmod hf hi) hsmall

end CFSG.Quasithin.ChapterK.Linear.Recognition.PSL3FourExclusion

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.PSL3FourExclusion
universe u v
variable {G : Type u} [Group G] [Finite G]
 {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
 {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}} {L : Subgroup G} [L.Normal]

/-- The actual faithful irreducible actor is sufficient; restriction to the
normal PSL₃(4) subgroup need not itself be irreducible. -/
theorem quadraticRatio_gt_two_of_irreducible
 (hsq : IsSQTK K G) (hm : ClassicalGroup.IsPSL L 3 4)
 (hquot : IsPGroup 2 (G ⧸ L)) (hcore : pCore 2 G = ⊥)
 (hf : Function.Injective ρ) (hi : ρ.IsIrreducible) :
 2 < quadraticRatio ρ := by
 by_contra hn
 have hsmall : quadraticRatio ρ ≤ 2 := le_of_not_gt hn
 obtain ⟨hqs,hz,_⟩ := model_facts hm
 let : IsQuasisimple L := hqs
 let : IsSimpleGroup (L ⧸ center L) := hqs.simple
 let : IsSimpleGroup L :=
   (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm).isSimpleGroup
 have hnc : ¬ IsMulCommutative L := by
   intro hab
   have he : center L = ⊤ := center_eq_top_iff.mpr hab
   rw [hz] at he
   exact bot_ne_top he
 have hc := centralizer_eq_bot_of_simple_two_quotient L hnc hquot hcore
 obtain ⟨J,hiJ,hfJ⟩ := exists_faithful_normal_simple_constituent ρ hf hi L
 obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
 have hdim := Representation.PSL3Four.finrank_gt_four_of_faithful hF e J.toRepresentation hfJ hiJ
 have hout := Matrix.PSL3Four.outer_two_rank_le_of_equiv hF e
 obtain ⟨A,hA,hq,hd⟩ := (quadraticRatio_le_two_iff ρ).mp hsmall
 have houter : A ⊓ L = ⊥ → rank A ≤ 2 := fun hdis =>
   (rank_le_outer_rank_of_disjoint L A hA hc hdis).trans hout
 have hstable := quadratic_constituent_stable_of_simple_of_outer_rank_two ρ L A J hiJ hdim hq houter hd
 exact not_quadratic_actor_preserving_simple hsq
   ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩ hquot hc J hfJ hiJ A hA hq hd hstable
end CFSG.Quasithin.ChapterK.Linear.Recognition.PSL3FourExclusion
