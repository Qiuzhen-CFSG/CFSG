module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.TableReduction.SourceClauses
public import Theory.GroupAction.CentralKernelFixedComponents
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M12Consequences
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
public import Theory.SpecificGroups.PSL3Two.Automorphisms

/-!
# M₁₂ and J₂ exclusions for the exceptional-cover argument

An A₅ component upstairs embeds as a component in the full fixed subgroup of
the induced central-quotient action. This uses the normality of the fixed-point
image under a central-kernel surjection, rather than an equality of fixed
subgroups. The outer J₂ row has order 336, so cannot contain this subgroup of
order 60; faithfulness of the quotient action then reflects innerness upstairs.

If an inner representative were 2-central in the actual central quotient, a
Sylow 2-subgroup would lie in the model's full fixed subgroup. The M₁₂ table
excludes its solvable branch and gives a strict Sylow intersection index in
each remaining branch. For J₂ the checked inner-class calculation gives fixed
subgroup index 2520, which is even and thus excludes Sylow containment.

The M₁₂ and outer J₂ arguments take the exact earlier involution tables as
explicit source input. The J₂ mark uses the already proved inner table.
These are the conditional deductions needed by the final assembly, not proofs
of exhaustiveness of the earlier source tables.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(4),(8), printed pp.1171–1172 / PDF pp.1188–1189, and the final paragraph
of 16.3.6, printed p.1179 / PDF p.1196.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
open Subgroup Theory.GroupTheory ClassificationModels
open Theory.GroupTheory.DoubleCoverCentralizer

private theorem center_bot_of_a5 {K : Type*} [Group K]
    (e : K ≃* alternatingGroup (Fin 5)) : center K = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  have hz' := (Subgroup.centerCongr e ⟨z, hz⟩).property
  change e z ∈ center (alternatingGroup (Fin 5)) at hz'
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz'
  exact mem_bot.mpr (e.map_eq_one_iff.mp hz')

/-- A component of an upstairs fixed subgroup survives in the complete fixed
subgroup of any central quotient model, with its actual A₅ equivalence. -/
theorem quotient_fixed_a5_component
    {H M : Type*} [Group H] [Group M]
    (J : Subgroup H) (r : MulAut H)
    (hJ : IsComponentIn J r.fixedSubgroup)
    (eJ : Nonempty (J ≃* alternatingGroup (Fin 5)))
    (e : H ⧸ center H ≃* M) :
    ∃ D : Subgroup (MulAut.centralQuotientAction e r).fixedSubgroup,
      IsComponent (MulAut.centralQuotientAction e r).fixedSubgroup D ∧
        Nonempty (D ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨eJ⟩ := eJ
  let K : Subgroup r.fixedSubgroup := J.subgroupOf r.fixedSubgroup
  let eK : K ≃* alternatingGroup (Fin 5) :=
    (Subgroup.subgroupOfEquivOfLe hJ.1).trans eJ
  have hK : IsComponent r.fixedSubgroup K := hJ.2
  have hZ : center K = ⊥ := center_bot_of_a5 eK
  let q : H →* M := e.toMonoidHom.comp (QuotientGroup.mk' (center H))
  have hq : Function.Surjective q := e.surjective.comp
    (QuotientGroup.mk'_surjective (center H))
  have hker : q.ker ≤ center H := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    exact (MonoidHom.mem_ker.mp hx).trans (e.map_one).symm
  have heq : ∀ x, q (r x) = MulAut.centralQuotientAction e r (q x) := by
    intro x
    exact (MulAut.centralQuotientAction_apply e r x).symm
  obtain ⟨hD, hDe⟩ := MulAut.fixedSubgroupMap_component_of_center_eq_bot
    r (MulAut.centralQuotientAction e r) q hq hker heq K hK hZ
  refine ⟨K.map (MulAut.fixedSubgroupMap r
      (MulAut.centralQuotientAction e r) q heq), hD, ?_⟩
  obtain ⟨eKD⟩ := hDe
  exact ⟨eKD.symm.trans eK⟩

private theorem twoCentral_fixed_sylow
    {H M : Type*} [Group H] [Group M] [Finite H]
    (e : H ⧸ center H ≃* M) (r : MulAut H) (f : H)
    (hf : MulAut.conj f = r)
    (h : TwoCentral (QuotientGroup.mk' (center H) f)) :
    ∃ S : Sylow 2 M,
      (S : Subgroup M) ≤ (MulAut.centralQuotientAction e r).fixedSubgroup := by
  let : Finite M := Finite.of_surjective e e.surjective
  obtain ⟨S, hu, hz⟩ := h
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  intro x hx
  change x ∈ (S : Subgroup (H ⧸ center H)).map e.toMonoidHom at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [MulAut.mem_fixedSubgroup]
  rw [← hf, MulAut.centralQuotientAction_conj]
  have hc := congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)
  change y * QuotientGroup.mk' (center H) f = QuotientGroup.mk' (center H) f * y at hc
  change e (QuotientGroup.mk' (center H) f) * e y *
    (e (QuotientGroup.mk' (center H) f))⁻¹ = e y
  apply mul_inv_eq_iff_eq_mul.mpr
  simpa only [map_mul] using congrArg e hc.symm

variable {H : Type*} [Group H] [IsQuasisimple H]

/-- The M₁₂ table rules out a 2-central quotient representative of an
involution whose fixed subgroup has the specified A₅ component. -/
theorem m12_not_twoCentral_of_component [Finite H] (tables : InvolutionTables)
    (J : Subgroup H) (r : MulAut H) (hr : orderOf r = 2)
    (hJ : IsComponentIn J r.fixedSubgroup)
    (eJ : Nonempty (J ≃* alternatingGroup (Fin 5)))
    (e : H ⧸ center H ≃* SporadicName.m12.Carrier)
    (f : H) (hf : MulAut.conj f = r)
    (_hf2 : orderOf (QuotientGroup.mk' (center H) f) = 2) :
    ¬ TwoCentral (QuotientGroup.mk' (center H) f) := by
  intro htwo
  obtain ⟨D, hD, _⟩ := quotient_fixed_a5_component J r hJ eJ e
  have hr' : orderOf (MulAut.centralQuotientAction e r) = 2 :=
    (orderOf_injective _ (MulAut.centralQuotientAction_injective e) r).trans hr
  obtain ⟨S, hS⟩ := twoCentral_fixed_sylow e r f hf htwo
  have hindex : 2 < (MulAut.centralQuotientAction e r).fixedSubgroup.relIndex
      (S : Subgroup SporadicName.m12.Carrier) :=
    OtherPreliminaries.Mathieu.m12_component_index_of_alternative
      _ (tables.m12 _ hr') D hD S
  rw [Subgroup.relIndex_eq_one.mpr hS] at hindex
  omega

/-- The outer J₂ fixed subgroup has order 336 and cannot contain the
transported A₅ component of order 60. Thus the upstairs action is inner. -/
theorem j2_inner_of_component (tables : InvolutionTables)
    (J : Subgroup H) (r : MulAut H) (hr : orderOf r = 2)
    (hJ : IsComponentIn J r.fixedSubgroup)
    (eJ : Nonempty (J ≃* alternatingGroup (Fin 5)))
    (e : H ⧸ center H ≃* SporadicName.j2.Carrier) :
    ∃ f : H, r = MulAut.conj f := by
  obtain ⟨D, _, ⟨eD⟩⟩ := quotient_fixed_a5_component J r hJ eJ e
  have hr' : orderOf (MulAut.centralQuotientAction e r) = 2 :=
    (orderOf_injective _ (MulAut.centralQuotientAction_injective e) r).trans hr
  apply (MulAut.centralQuotientAction_inner_iff e r).mp
  rcases tables.j2 _ hr' with ⟨hi, _⟩ | ⟨_, ⟨eF⟩⟩
  · exact hi
  · have hcardD : Nat.card D = 60 := by
      rw [Nat.card_congr eD.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hcardF : Nat.card (MulAut.centralQuotientAction e r).fixedSubgroup = 336 :=
      (Nat.card_congr eF.toEquiv).trans Matrix.PSL3Two.Automorphisms.card_aut
    have hd := D.card_subgroup_dvd_card
    rw [hcardD, hcardF] at hd
    norm_num at hd

/-- In J₂ an inner fixed subgroup with a component has even index 2520,
which excludes containment of a Sylow 2-subgroup and hence 2-centrality. -/
theorem j2_not_twoCentral_of_component [Finite H]
    (J : Subgroup H) (r : MulAut H) (hr : orderOf r = 2)
    (hJ : IsComponentIn J r.fixedSubgroup)
    (eJ : Nonempty (J ≃* alternatingGroup (Fin 5)))
    (e : H ⧸ center H ≃* SporadicName.j2.Carrier)
    (f : H) (hf : MulAut.conj f = r)
    (_hf2 : orderOf (QuotientGroup.mk' (center H) f) = 2) :
    ¬ TwoCentral (QuotientGroup.mk' (center H) f) := by
  let : Finite SporadicName.j2.Carrier := Finite.of_surjective e e.surjective
  intro htwo
  obtain ⟨D, hD, _⟩ := quotient_fixed_a5_component J r hJ eJ e
  have hr' : orderOf (MulAut.centralQuotientAction e r) = 2 :=
    (orderOf_injective _ (MulAut.centralQuotientAction_injective e) r).trans hr
  have hi : ∃ g, MulAut.centralQuotientAction e r = MulAut.conj g :=
    (MulAut.centralQuotientAction_inner_iff e r).mpr ⟨f, hf.symm⟩
  have hindex : (MulAut.centralQuotientAction e r).fixedSubgroup.index = 2520 :=
    OtherPreliminaries.JankoTwoHigmanSims.J2Inner.inner_component_index
      _ hr' hi D hD
  obtain ⟨S, hS⟩ := twoCentral_fixed_sylow e r f hf htwo
  have hd : 2 ∣ (MulAut.centralQuotientAction e r).fixedSubgroup.index := by
    rw [hindex]
    decide
  exact S.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hS))

end CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
