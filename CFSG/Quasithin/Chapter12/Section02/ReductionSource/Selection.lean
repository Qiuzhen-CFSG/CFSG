module
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient
public import Theory.Representation.BinaryOffender.Homogeneous.Existence
/-!
# Choosing the original reduced module in the normalized source case

When T already normalizes L, the faithful intrinsic module V(L) gives a
nontrivial commutator [R₂(LT),L] by A.4.11. Quasisimplicity of L/O₂(L)
supplies the required central two-chief factors. The perfect actor therefore
has an Irr⁺ section, and A.1.42 selects a homogeneous member under the actual
Sylow subgroup. Its literal ambient image is the chosen subgroup V.

This is the normalized selection step of Theorem 12.2.2, used in the
remaining linear-three branch of 13.1.4. It does not assume a chosen module,
a module classification, or the general normalization theorem 10.0.1.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Theorem 12.2.2, pp.794--795; A.4.11 and A.1.42, pp.61 and 32.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G}

private theorem central_two_chief_of_quasisimple
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q] :
    HasCentralPChiefFactors 2 Q := by
  let e : (Q ⧸ (⊥ : Subgroup Q)) ≃* Q := QuotientGroup.quotientBot
  let : IsQuasisimple (Q ⧸ (⊥ : Subgroup Q)) :=
    IsQuasisimple.of_mulEquiv e.symm
  exact hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
    (⊥ : Subgroup Q) (by simp) inferInstance

/-- The same L acts nontrivially on the actual R₂(LT). -/
theorem Hypothesis1221.reduced_commutator_ne_bot
    (h : Hypothesis1221 K T L) (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ⁅reducedTwoSubgroup (L ⊔ (T : Subgroup G) : Subgroup G),
      L.subgroupOf (L ⊔ (T : Subgroup G))⁆ ≠ ⊥ := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  let e : A ≃* L := subgroupOfEquivOfLe le_sup_left
  have hp : IsPPerfect 2 A :=
    h.maximal_faithful.2.1.2.1.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hmap : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  have hne : ChapterA.Section04.intrinsicSignalizerModule A ≠ ⊥ := by
    intro he
    apply h.maximal_faithful.2.2
    rw [← hmap, ChapterA.Section04.intrinsicSignalizerModule_map_of_injective
      H.subtype H.subtype_injective, he, Subgroup.map_bot]
  let eQ := QuotientGroup.congr (pCore 2 A) (pCore 2 L) e (pCore_map_iso 2 e)
  let := h.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) :=
    IsQuasisimple.of_mulEquiv eQ.symm
  have hc : HasCentralPChiefFactorsAbove 2 (pCore 2 A) :=
    (hasCentralPChiefFactorsAbove_iff_quotient _).mpr central_two_chief_of_quasisimple
  exact ChapterA.Section04.reduced_commutator_ne_bot_of_intrinsicModule_ne_bot A
    (show A.Normal from inferInstance).isSubnormal hp hc hne

/-- The original hypotheses and already available normalization construct a
homogeneous chosen module on the literal reduced subgroup. -/
theorem Hypothesis1221.exists_chosen_of_normalizes
    (h : Hypothesis1221 K T L) (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ V : Subgroup G, Nonempty (ChosenModule T L V) := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  let e : A ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hnot : ¬ (⊤ : Submodule (ZMod 2) (Additive (ReducedModule H))) ≤
      fixedSpace (reducedRepresentation H) A := by
    intro hf
    apply h.reduced_commutator_ne_bot hn
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv x hx
    have hh := congrArg (fun w : Additive (ReducedModule H) => w.toMul.val)
      (hf (show Additive.ofMul (⟨v, hv⟩ : ReducedModule H) ∈ ⊤ from trivial) ⟨x, hx⟩)
    change x * v * x⁻¹ = v at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨I, hI⟩ := exists_isIrrPlus_of_not_fixed (reducedRepresentation H) A hnot
  have hT : (T : Subgroup G).subgroupOf H ≤ normalizer (A : Set H) :=
    le_normalizer_of_normal
  obtain ⟨J, _, hJ⟩ := exists_isIrrPlusWith_le_orbitSpan (reducedRepresentation H)
    hT T.isPGroup'.comap_subtype hI
  exact ⟨subspaceImage H J, ⟨⟨J, hJ, rfl⟩⟩⟩
end CFSG.Quasithin.Chapter12.Section02
