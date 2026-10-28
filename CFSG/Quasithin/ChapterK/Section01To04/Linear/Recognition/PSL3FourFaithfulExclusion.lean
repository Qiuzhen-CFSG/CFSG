module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.PSL3FourChiefExclusion
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Faithful PSL₃(4) actions have quadratic ratio greater than two

No irreducibility hypothesis is needed when the acting group has trivial
two-core and a normal PSL₃(4) subgroup with two-group quotient. The simple
normal subgroup lies in every nontrivial normal subgroup. A literal
irreducible section detecting it is therefore faithful on the whole actor.
Quadraticity and fixed codimension pass to that same section, contradicting
the previously proved irreducible exclusion.

The actual FSU application is `Chapter3.Section02.LinearThreeFourGraphFixedSpace`.
It excludes FF action before any assertion about invariance of the seed.
Source: Aschbacher–Smith B.4.2–5 and 3.2.2(6), 3.2.8–9, printed pp.86–87
and579–583 (refs/quasithin.pdf).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.PSL3FourExclusion
universe u v
variable {G : Type u} [Group G] [Finite G]
 {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
 {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}} {L : Subgroup G} [L.Normal]

/-- Every faithful action of the original reduced almost simple actor has
quadratic ratio greater than two. The component and quotient are unchanged. -/
theorem quadraticRatio_gt_two_of_faithful
 (hsq : IsSQTK K G) (hm : ClassicalGroup.IsPSL L 3 4)
 (hquot : IsPGroup 2 (G ⧸ L)) (hcore : pCore 2 G = ⊥)
 (hf : Function.Injective ρ) : 2 < quadraticRatio ρ := by
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
 have hstructure := simple_two_quotient_structure L hnc hquot hcore
 have hn : ¬ L ≤ ρ.ker := by
   intro h
   exact (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
     (bot_unique (h.trans ((MonoidHom.ker_eq_bot_iff ρ).mpr hf).le))
 obtain ⟨U,N,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect L hn
 let σ := N.quotientRepresentation
 have hfaith : Function.Injective σ := by
   apply (MonoidHom.ker_eq_bot_iff σ).mp
   by_contra hk
   exact hn (hstructure.2.2 σ.ker inferInstance hk)
 by_contra hnq
 have hsmall : quadraticRatio ρ ≤ 2 := le_of_not_gt hnq
 obtain ⟨A,hA,hquad,hbound⟩ := (quadraticRatio_le_two_iff ρ).mp hsmall
 have hqU := quadratic_subrepresentation ρ U hquad
 have hqN : IsQuadratic σ A :=
   quadratic_of_equivariant_surjection U.toRepresentation σ
     N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hqU
 have hcN : fixedCodim σ A ≤ 2 * rank A := by
   change fixedCodim N.quotientRepresentation A ≤ 2 * rank A
   have hU := fixedCodim_subrepresentation_le ρ U A
   have hN := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
   omega
 exact not_le_of_gt (quadraticRatio_gt_two_of_irreducible hsq hm hquot hcore hfaith hi)
   ((quadraticRatio_le_two_iff σ).mpr ⟨A,hA,hqN,hcN⟩)

/-- In particular the original faithful action is not an FF module. -/
theorem not_isFFModule_of_faithful
 (hsq : IsSQTK K G) (hm : ClassicalGroup.IsPSL L 3 4)
 (hquot : IsPGroup 2 (G ⧸ L)) (hcore : pCore 2 G = ⊥)
 (hf : Function.Injective ρ) : ¬ IsFFModule ρ := by
 intro hff
 exact not_le_of_gt (quadraticRatio_gt_two_of_faithful hsq hm hquot hcore hf)
   (((isFFModule_iff_quadraticRatio_le_one ρ).mp hff).trans (by norm_num))
end CFSG.Quasithin.ChapterK.Linear.Recognition.PSL3FourExclusion
