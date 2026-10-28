module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Theory.GroupAction.AutomorphismFixedResidual
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.QuotientCriterion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Fusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Noncentral
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.QuotientActions

/-!
# Fixed-perfect-residual cores for every inner J₂ involution

Every involution of the actual degree-100 ATLAS carrier is conjugate to the
checked representatives `a` or `t = (abab⁻¹)⁶`. For `a`, the whole centralizer
is the constructed product E₄ × A₅. For `t`, the existing five-block action
surjects onto A₅, and the centralizer order 1920 gives kernel order 32.
Thus both fixed subgroups have an actual A₅ quotient with two-group kernel.

The quotient criterion makes the inner image of the fixed perfect residual
three-core-free. Its centralizer inside the involution centralizer has a
two-group inner kernel and a two-group outer image, hence order prime to three.
All maps refer to the original carrier and the literal solvable residual;
no alternate realization, centralizer-shape assumption, or model premise remains.

Source: GLS3, Table 5.3g and notes (3)–(4), and the J₂ case of the argument
on Aschbacher--Smith printed p.1137 (combined manuscript, 1 March 2004).
The adapted class-2B certificate modules preserve their Chapter 16 originals
and their attribution to the retained ATLAS J2G1-p100B0 data.
-/

public section
namespace Sporadic.LeechRelated.J2.InnerInvolutionCores
open Subgroup GeneratorPair ExceptionalParabolics

private theorem kernel_card {F : Type*} [Group F]
    (f : F →* alternatingGroup (Fin 5)) (hf : Function.Surjective f) :
    Nat.card f.ker * 60 = Nat.card F := by
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top,
    nat_card_alternatingGroup, Nat.card_fin] at h
  exact h

private noncomputable def aQuotient :
    centralizer ({a} : Set Carrier) →* alternatingGroup (Fin 5) :=
  (MonoidHom.snd E4 A5).comp a_centralizer_equiv.toMonoidHom

private theorem aQuotient_surjective : Function.Surjective aQuotient := by
  intro x
  exact ⟨a_centralizer_equiv.symm (1, x),
    congrArg Prod.snd (a_centralizer_equiv.apply_symm_apply (1, x))⟩

private theorem aQuotient_kernel : IsPGroup 2 aQuotient.ker := by
  apply IsPGroup.of_card (n := 2)
  have h := kernel_card aQuotient aQuotient_surjective
  have hc : Nat.card (centralizer ({a} : Set Carrier)) = 240 := by
    rw [Nat.card_congr a_centralizer_equiv.toEquiv, Nat.card_prod,
      nat_card_alternatingGroup, Nat.card_fin]
    norm_num [E4, C2, Nat.card_fun, Nat.factorial]
  rw [hc] at h
  omega

private theorem tQuotient_kernel :
    IsPGroup 2 FirstParabolic.QuotientActions.innerAction.ker := by
  apply IsPGroup.of_card (n := 5)
  have h := kernel_card FirstParabolic.QuotientActions.innerAction
    FirstParabolic.QuotientActions.innerAction_surjective
  rw [FirstParabolic.card_l₁] at h
  omega

private theorem data_of_fixed_equiv {F : Type*} [Group F]
    (r : MulAut Carrier) (e : r.fixedSubgroup ≃* F)
    (f : F →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    MulAut.FixedResidualThreeCoreData r :=
  fixedResidualThreeCoreData_of_quotient r (f.comp e.toMonoidHom)
    (hf.comp e.surjective) (hk.comap_of_injective e.toMonoidHom e.injective)

/-- Both literal calculations for the noncentral inner representative, class 2B. -/
theorem a_fixedResidualThreeCoreData : MulAut.FixedResidualThreeCoreData (MulAut.conj a) :=
  data_of_fixed_equiv _ (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj a))
    aQuotient aQuotient_surjective aQuotient_kernel

/-- Both literal calculations for the central inner representative, class 2A. -/
theorem t_fixedResidualThreeCoreData :
    MulAut.FixedResidualThreeCoreData (MulAut.conj FirstFusion.t) :=
  data_of_fixed_equiv _ (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj FirstFusion.t))
    FirstParabolic.QuotientActions.innerAction
    FirstParabolic.QuotientActions.innerAction_surjective tQuotient_kernel

/-- Every inner involution on the actual degree-100 carrier satisfies the exact
fixed-perfect-residual criterion, with no additional model hypotheses. -/
theorem inner_fixedResidualThreeCoreData (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : r ∈ (MulAut.conj : Carrier →* MulAut Carrier).range) :
    MulAut.FixedResidualThreeCoreData r := by
  have hin : ∃ g : Carrier, r = MulAut.conj g := by
    obtain ⟨g, hg⟩ := hi
    exact ⟨g, hg.symm⟩
  rcases inner_fixed_representatives r hr hin with he | he
  · obtain ⟨e⟩ := he
    exact data_of_fixed_equiv r e aQuotient aQuotient_surjective aQuotient_kernel
  · obtain ⟨e⟩ := he
    exact data_of_fixed_equiv r e FirstParabolic.QuotientActions.innerAction
      FirstParabolic.QuotientActions.innerAction_surjective tQuotient_kernel

/-- Application to the literal intermediate automorphism subgroup used by the
central-cover J₂ action argument on printed p.1137. -/
theorem inner_threeCore_eq_bot (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : r ∈ (MulAut.conj : Carrier →* MulAut Carrier).range)
    (D : Subgroup (MulAut Carrier))
    (hD : D ≤ centralizer ({r} : Set (MulAut Carrier)))
    (hR : MulAut.fixedPerfectResidualInner r ≤ D) : pCore 3 D = ⊥ :=
  MulAut.threeCore_eq_bot_of_fixedResidualData r (inner_fixedResidualThreeCoreData r hr hi)
    D hD hR

end Sporadic.LeechRelated.J2.InnerInvolutionCores
