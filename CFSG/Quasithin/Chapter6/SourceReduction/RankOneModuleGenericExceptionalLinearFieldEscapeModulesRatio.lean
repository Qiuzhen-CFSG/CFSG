module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.PSL3FourChiefExclusion
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.Representation.BinaryOffender.QuadraticSection
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.Basic
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.Quasithin.Rank

/-!
# Faithful PSL₃(4) actions have strict quadratic ratio

A nontrivial perfect residual survives on a literal irreducible subquotient.
Every nontrivial normal subgroup of the core-free actor contains its simple
residual, so this section is faithful. A putative quadratic actor retains
its rank on the section while its fixed codimension decreases. The proved
PSL₃(4) chief-action exclusion then supplies the strict bound.

The application below uses the original H/O₂(H) action on U/Z and identifies
its residual by the actual quotient map. No irreducibility of U/Z, Fitting
identity, diagram condition, or numerical callback is assumed. This proves
the quadratic obstruction in the final paragraph of 5.1.14; the cubic
constituent argument establishing abelianness in 5.1.23 is separate.

Source: Aschbacher--Smith, printed pp.645--646, refs/quasithin.pdf.
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape

universe u v
variable {X : Type u} [Group X] [Finite X]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {κ : GroupClass.{u}}

private theorem strict (ρ : Representation (ZMod 2) X W) (K : Subgroup X) [K.Normal]
    (hsq : IsSQTK κ X) (hm : ClassicalGroup.IsPSL K 3 4)
    (hquot : IsPGroup 2 (X ⧸ K)) (hcore : pCore 2 X = ⊥)
    (hf : Function.Injective ρ) : 2 < quadraticRatio ρ := by
  obtain ⟨hqs, hz, _⟩ := ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm
  let : IsQuasisimple K := hqs
  let : IsSimpleGroup (K ⧸ center K) := hqs.simple
  let : IsSimpleGroup K :=
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm).isSimpleGroup
  have hnc : ¬ IsMulCommutative K := by
    intro ha
    have he := center_eq_top_iff.mpr ha
    rw [hz] at he
    exact bot_ne_top he
  have hnormal := (simple_two_quotient_structure K hnc hquot hcore).2.2
  have hn : ¬ K ≤ ρ.ker := by
    intro h
    have hb : K = ⊥ := le_bot_iff.mp (h.trans ((MonoidHom.ker_eq_bot_iff ρ).mpr hf).le)
    exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance hb
  obtain ⟨U, N, hi, hnN⟩ :=
    Representation.QuadraticFourGroup.exists_irreducible_section_surviving_perfect K hn
  have hfN : Function.Injective N.quotientRepresentation := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    by_contra hne
    exact hnN (hnormal _ inferInstance hne)
  by_contra hnot
  obtain ⟨A, hA, hquad, hc⟩ := (quadraticRatio_le_two_iff ρ).mp (le_of_not_gt hnot)
  have hquadN := quadratic_of_equivariant_surjection U.toRepresentation N.quotientRepresentation
    N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ U hquad)
  have hcN : fixedCodim N.quotientRepresentation A ≤ 2 * rank A := by
    have hU := fixedCodim_subrepresentation_le ρ U A
    have hN := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
    omega
  have hsmall := (quadraticRatio_le_two_iff N.quotientRepresentation).mpr ⟨A,hA,hquadN,hcN⟩
  exact not_le_of_gt
    (ChapterK.Linear.Recognition.PSL3FourExclusion.quadraticRatio_gt_two_of_irreducible
      hsq hm hquot hcore hfN hi) hsmall


/-- The strict bound on every faithful literal H/O₂(H)-action. All residual,
core and chief-section premises are discharged from the supplied PSL₃(4) quotient. -/
public theorem localQuotientAction_quadraticRatio_gt_two {G : Type u} [Group G] [Finite G] (H U Z : Subgroup G)
    [IsElementaryAbelian 2 U] (hH : IsSQTK κ H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (a : Chapter15.Section03.AbelianAmalgam.LocalQuotientAction H U Z) :
    2 < quadraticRatio a.representation := by
  let Q := H ⧸ pCore 2 H
  let K : Subgroup Q := (pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))
  let : K.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hsq : IsSQTK κ Q := by
    refine ⟨?_, hH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho
      (pCore 2 H) pCore_isPGroup).trans (hH.stronglyQuasithin p hp ho)
  have hmodel : ClassicalGroup.IsPSL K 3 4 :=
    hm.of_mulEquiv (coreQuotientEquivImage 2 (pResidual 2 H)).symm
  have hr : K = pResidual 2 Q := map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)
  have hquot : IsPGroup 2 (Q ⧸ K) := by
    exact (pResidual_le_iff_isPGroup_quotient 2 K).mp hr.ge
  exact strict a.representation K hsq hmodel hquot
    (pCore_quotient_pCore_eq_bot 2) a.faithful

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
