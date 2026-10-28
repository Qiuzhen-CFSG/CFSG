module
public import Theory.Representation.BinaryOffender.Stability
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer

/-!
# Detecting a component in the best-offender subgroup after reduction

Let B be a normal quasisimple component in a binary actor H. Suppose a
surjection to a group with trivial two-core sends B onto its generalized
Fitting subgroup. A best offender with nontrivial reduced image forces B
into the whole action's best-offender subgroup. Otherwise component
normality makes the two subgroups commute; the reduced offender then lies
in a normal abelian subgroup of odd order, a contradiction.

The argument allows a nontrivial two-core in H and an even covering center
in B. It is used on the entire central sections in the nonbinary MS argument.
Source: Aschbacher--Smith B.1.7, B.5.1 and C.1.34, pp.70--71, 99--102,
136--137; MS93, the offender-generated component in Section 3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {H H₀ W : Type*} [Group H] [Group H₀] [Finite H₀]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- An offender surviving the reduction forces the original covering component
into the actual best-offender subgroup. -/
theorem component_le_offenderSubgroup_of_reduced_image
    (ρ : Representation (ZMod 2) H W) (B : Subgroup H) [B.Normal] [IsQuasisimple B]
    (f : H →* H₀) (hf : Function.Surjective f)
    (hfit : generalizedFitting H₀ = B.map f) (hcore : pCore 2 H₀ = ⊥)
    (A : Subgroup H) (hA : IsBestOffender ρ A) (hne : A.map f ≠ ⊥) :
    B ≤ offenderSubgroup ρ := by
  let O := offenderSubgroup ρ
  let : O.Normal := offenderSubgroup_normal ρ
  rcases IsComponent.normal_dichotomy
    (⟨(inferInstance : B.Normal).isSubnormal,inferInstance⟩ : IsComponent H B) O with hb | hc
  · exact hb
  · have hOC : O.map f ≤ centralizer (B.map f : Set H₀) := by
      apply le_centralizer_iff.mp
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [←map_commutator,hc,Subgroup.map_bot]
    have hOB : O.map f ≤ B.map f := hOC.trans (hfit ▸ centralizer_generalizedFitting_le H₀)
    let : (O.map f).Normal := Normal.map inferInstance f hf
    let : IsMulCommutative (O.map f) :=
      ⟨⟨fun a b => Subtype.ext (hOC a.property b (hOB b.property)).symm⟩⟩
    have hOF : O.map f ≤ fittingSubgroup H₀ := le_sSup ⟨inferInstance,inferInstance⟩
    have hAO : A.map f ≤ pPrimeCore 2 H₀ :=
      (map_mono (hA.le_offenderSubgroup ρ)).trans
        (hOF.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))
    let : IsElementaryAbelian 2 A := hA.1.2
    have hp : IsPGroup 2 (A.map f) := (IsElementaryAbelian.isPGroup 2 A).map f
    obtain ⟨m,hm⟩ := hp.exists_card_eq
    have hcop : Nat.Coprime (Nat.card (A.map f)) (Nat.card (pPrimeCore 2 H₀)) := by
      rw [hm]
      exact (pPrimeCore_coprime_card (p := 2) (G := H₀)).pow_left m
    exact (hne (le_bot_iff.mp ((le_inf le_rfl hAO).trans
      (disjoint_of_coprime_natCard hcop).le_bot))).elim
end Representation.BinaryOffender
