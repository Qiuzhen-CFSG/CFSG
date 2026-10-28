module
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.SourceCentralizer
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalAutomizerSource
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank

/-!
# The original A₆ quotient supplies the centralizer argument

An actual A₆ component is normal by the proved obstruction to commuting A₆
subgroups in a quasithin group. The literal conjugation action on that component
has kernel O₂(H). The original quotient isomorphism with Aut(A₆) therefore
makes its action image have full order, proving surjectivity without assuming
that the quotient isomorphism preserves the component or its action.

Applying the original-source centralizer theorem now needs neither the general
2.5.20 normality result nor an additional compatible-action witness. The genuine
2.5.21 quotient conclusion remains explicit, with the original component model.

Source: Aschbacher--Smith, 2.5.21 and the following A₆ reduction, printed
pp.565--567, followed by 2.5.22(2), p.567.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.A6Shadow
open ComponentRefinement Section05.ComponentSelection
variable {G:Type*} [Group G] [Finite G] {H K M:Subgroup G} {S:Sylow 2 H} {z:G}

/-- Original source 2.5.22(2), supplied directly by the literal 2.5.21 quotient
and A₆ component. Normality, the original surjective action and its compatibility
are proved internally; the earlier-source endpoint constructs the crossing data. -/
theorem centralizer_eq_of_original_quotient
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    (hstar:H∈gammaStar (Chapter1.He G) M)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype))
    (eK:K≃*alternatingGroup (Fin 6))
    (eQ:(H⧸pCore 2 H)≃*AlternatingSix.ShadowLocal.AutA6) :
    H=centralizer ({t}:Set G) := by
  let D:=K.subgroupOf H
  let eD:D≃*alternatingGroup (Fin 6):=(subgroupOfEquivOfLe c.component_le).trans eK
  let : D.Normal:=alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D eD c.component
  let f:H→*AlternatingSix.ShadowLocal.AutA6:=
    AlternatingSix.ShadowLocal.conjugationAction D eD
  have hk:f.ker=pCore 2 H:=by
    rw [show f=(MulAut.congr eD).toMonoidHom.comp (MulAut.conjNormal:H→*MulAut D) from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.congr eD).injective]
    exact MathieuSourceSetup.normal_component_conjugation_ker c hG hempty hgen
  have hf:Function.Surjective f:=by
    apply MonoidHom.range_eq_top.mp
    apply f.range.eq_top_of_card_eq
    rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hk).toEquiv]
    exact Nat.card_congr eQ.toEquiv
  apply centralizer_eq_of_original_source c hG hempty hgen hb hstar t ht htC htZ eK f hf
  intro h k
  let d:D:=(subgroupOfEquivOfLe c.component_le).symm k
  have he:eD d=eK k:=by simp only [eD,d,MulEquiv.trans_apply,MulEquiv.apply_symm_apply]
  rw [←he,show f=AlternatingSix.ShadowLocal.conjugationAction D eD from rfl,
    AlternatingSix.ShadowLocal.conjugationAction_apply]
  simp only [eD,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
  exact congrArg Subtype.val (MulAut.conjNormal_apply h d)
end CFSG.Quasithin.Chapter2.A6Shadow
