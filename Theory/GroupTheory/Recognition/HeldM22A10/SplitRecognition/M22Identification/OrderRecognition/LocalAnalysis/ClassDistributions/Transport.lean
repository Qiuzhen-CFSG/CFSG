module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions.Model

/-!
# Transport of class counts to the original Sylow subgroup

The standard coordinate Sylow need not map to `D.sylow`. Sylow conjugacy
inside `D.centralizer` gives an isomorphism whose underlying elements are
ambient conjugates. Thus it preserves every ambient conjugacy predicate.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 13, p.14; Sylow's conjugacy theorem.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CaseII.Distribution

local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

private def coordinateSylow : Sylow 2 TwistedModel :=
  Sylow.ofCard modelSylow (by
    rw [modelSylow_card]
    have h : Nat.card TwistedModel = 384 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [h]
    decide +kernel)

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Conjugating Sylows inside the centralizer preserves ambient classes. -/
public theorem sylow_class_card (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (r : TwistedModel) :
    Nat.card {x : D.sylow // IsConj (x : G) (into D k r)} =
      Nat.card {x : modelSylow // IsConj (into D k x) (into D k r)} := by
  let P : Sylow 2 D.centralizer := coordinateSylow.mapSurjective (f := k.toMonoidHom) k.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D.centralizer P D.localSylow
  let e₁ : modelSylow ≃* P :=
    modelSylow.equivMapOfInjective k.toMonoidHom k.injective
  let e₂ : P ≃* D.localSylow := (P.equivSMul g).trans
    (MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hg))
  let e₃ : D.localSylow ≃* D.sylow :=
    Subgroup.subgroupOfEquivOfLe D.sylow_le_centralizer
  let e := (e₁.trans e₂).trans e₃
  have he (x : modelSylow) : IsConj (into D k x) ((e x : D.sylow) : G) := by
    apply isConj_iff.mpr
    exact ⟨(g : G), rfl⟩
  symm
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
  intro x
  exact ⟨fun h => (he x).symm.trans h, fun h => (he x).trans h⟩

omit [Finite G] in
/-- The centralizer itself is transported by the specified equivalence. -/
public theorem centralizer_class_card (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (r : TwistedModel) :
    Nat.card {x : D.centralizer // IsConj (x : G) (into D k r)} =
      Nat.card {x : TwistedModel // IsConj (into D k x) (into D k r)} := by
  symm
  exact Nat.card_congr (Equiv.subtypeEquiv k.toEquiv (fun _ => Iff.rfl))

end CaseII.Distribution
end Theory.GroupTheory.HeldM22A10.M22Identification
