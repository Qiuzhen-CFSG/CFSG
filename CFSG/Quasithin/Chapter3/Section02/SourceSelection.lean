module
public import CFSG.Quasithin.Chapter3.Section02.Basic
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient
public import Theory.Representation.BinaryOffender.Homogeneous.Existence
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Constructing the original Fundamental Setup

A.4.11 applies to the original subnormal local C-component L, using its
faithful intrinsic module and quasisimple two-core quotient. Thus L moves
R₂(⟨L,T⟩), so the perfect T-orbit L₀ also moves that same reduced subgroup.
A minimal moved subspace gives an Irr⁺ constituent, and A.1.42 makes the
actual homogeneous choice under T. Neither normalization of L nor a
previously chosen module is assumed.

This supplies the existence assertion used at the start of Chapter 10,
including its nonnormal case. It also removes the constituent-existence
premise from the source selection in Lemma 3.2.3.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 3.2.3, p.580, and the opening of §10.1, p.741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem central_two_chief_of_quasisimple
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q] :
    HasCentralPChiefFactors 2 Q := by
  let e : (Q ⧸ (⊥ : Subgroup Q)) ≃* Q := QuotientGroup.quotientBot
  let : IsQuasisimple (Q ⧸ (⊥ : Subgroup Q)) :=
    IsQuasisimple.of_mulEquiv e.symm
  exact hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
    (⊥ : Subgroup Q) (by simp) inferInstance

/-- The original faithful component moves R₂(⟨L,T⟩), without normality of L. -/
theorem source_component_reduced_commutator_ne_bot
    (T : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    ⁅reducedTwoSubgroup (L ⊔ (T : Subgroup G) : Subgroup G),
      L.subgroupOf (L ⊔ (T : Subgroup G))⁆ ≠ ⊥ := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let e : A ≃* L := subgroupOfEquivOfLe le_sup_left
  have hp : IsPPerfect 2 A := hf.1.2.1.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hmap : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  have hne : ChapterA.Section04.intrinsicSignalizerModule A ≠ ⊥ := by
    intro he
    apply hf.2
    rw [← hmap, ChapterA.Section04.intrinsicSignalizerModule_map_of_injective
      H.subtype H.subtype_injective, he, Subgroup.map_bot]
  let eQ := QuotientGroup.congr (pCore 2 A) (pCore 2 L) e (pCore_map_iso 2 e)
  let := hq
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eQ.symm
  have hc : HasCentralPChiefFactorsAbove 2 (pCore 2 A) :=
    (hasCentralPChiefFactorsAbove_iff_quotient _).mpr central_two_chief_of_quasisimple
  exact ChapterA.Section04.reduced_commutator_ne_bot_of_intrinsicModule_ne_bot A
    hL.1.subnormal hp hc hne

/-- The actual T-orbit actor also moves the reduced subgroup on which the source
chooses its constituent. -/
theorem source_orbit_reduced_commutator_ne_bot
    (T : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    ⁅ReducedNormal.ModuleGroup (localJoin T L),
      (localOrbit T L).subgroupOf (localJoin T L)⁆ ≠ ⊥ := by
  have hn := source_component_reduced_commutator_ne_bot T L hL hf hq
  change ⁅reducedTwoSubgroup (localOrbit T L ⊔ (T : Subgroup G) : Subgroup G),
    (localOrbit T L).subgroupOf (localOrbit T L ⊔ (T : Subgroup G))⁆ ≠ ⊥
  rw [show localOrbit T L ⊔ (T : Subgroup G) = L ⊔ (T : Subgroup G) from
    componentOrbit_sup L T]
  intro he
  apply hn
  exact bot_unique ((commutator_mono le_rfl (comap_mono (le_componentOrbit L T))).trans_eq he)

/-- Construct the genuine FSU from the original source hypotheses, with no
preselected Irr⁺ space and no normalization hypothesis. -/
theorem source_exists_fundamentalSetup
    {K : GroupClass.{u}} (hG : IsSimpleQTKE K G) (T : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    Nonempty (FundamentalSetup K T L) := by
  let H := localJoin T L
  let A := (localOrbit T L).subgroupOf H
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect hL.1
  let : Group.IsPerfect (localOrbit T L) := isPerfect_iSup_conjugates L T
  let e : A ≃* localOrbit T L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hnot : ¬ (⊤ : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup H))) ≤
      fixedSpace (ReducedNormal.representation H) A := by
    intro hf'
    apply source_orbit_reduced_commutator_ne_bot T L hL.1 hf hq
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv x hx
    have hh := congrArg (fun w : Additive (ReducedNormal.ModuleGroup H) => w.toMul.val)
      (hf' (show Additive.ofMul (⟨v, hv⟩ : ReducedNormal.ModuleGroup H) ∈ ⊤ from trivial)
        ⟨x, hx⟩)
    change x * v * x⁻¹ = v at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨I, hI⟩ := exists_isIrrPlus_of_not_fixed (ReducedNormal.representation H) A hnot
  obtain ⟨D, _, _⟩ := lemma_3_2_3_constituent hG T L hL hf hq I hI
  exact ⟨D⟩
end CFSG.Quasithin.Chapter3.Section02
