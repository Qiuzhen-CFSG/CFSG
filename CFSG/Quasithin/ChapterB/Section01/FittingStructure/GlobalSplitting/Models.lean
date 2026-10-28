module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.Basic
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.SL2.BinaryProjective

/-!
# The local odd cores and projective binary models

The local cubic subgroup is normal in XA, and XA has order six by its
actual symmetric-group equivalence. The odd core has odd order dividing
six and contains X, so it equals X under the literal subgroup inclusion.
The existing faithful three-point projective action identifies S₃ with
SL₂(2); composing with the actual central quotient gives PSL₂(2)=L₂(2).

These identify the core and group conventions needed in B.1.9(1–2).
Source: Aschbacher–Smith, B.1.9, printed p.71.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

namespace MinimalFittingPlane
variable {A : Subgroup G} (d : MinimalFittingPlane ρ A)
include d

/-- The order of the actual local subgroup, transported through its model. -/
theorem local_card : Nat.card ↥(⁅fittingSubgroup G, A⁆ ⊔ A) = 6 := by
  rw [Nat.card_congr d.model.toEquiv, Nat.card_perm, Nat.card_fin]
  decide

/-- O(XA) is X, with O(XA) embedded by the original subgroup inclusion. -/
theorem oddCore_eq [Finite G] :
    ⁅fittingSubgroup G, A⁆ =
      (pPrimeCore 2 ↥(⁅fittingSubgroup G, A⁆ ⊔ A)).map
        (⁅fittingSubgroup G, A⁆ ⊔ A).subtype := by
  let X := ⁅fittingSubgroup G, A⁆
  let H := X ⊔ A
  let R := X.subgroupOf H
  have hR : Nat.card R = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show X ≤ H from le_sup_left)).toEquiv).trans
      d.odd_card
  have hnorm : H ≤ normalizer (X : Set G) :=
    sup_le X.le_normalizer (normalizer_commutator_ge_right _ _)
  let : R.Normal := normal_subgroupOf_of_le_normalizer hnorm
  have hle : R ≤ pPrimeCore 2 H := le_sSup ⟨inferInstance, by rw [hR]; decide⟩
  have hdiv : Nat.card (pPrimeCore 2 H) ∣ 6 :=
    d.local_card ▸ (pPrimeCore 2 H).card_subgroup_dvd_card
  have hdiv3 : Nat.card (pPrimeCore 2 H) ∣ 3 :=
    (pPrimeCore_coprime_card (p := 2) (G := H)).symm.dvd_of_dvd_mul_left hdiv
  have he : R = pPrimeCore 2 H :=
    eq_of_le_of_card_ge hle (by rw [hR]; exact Nat.le_of_dvd (by decide) hdiv3)
  calc
    X = R.map H.subtype := (map_subgroupOf_eq_of_le (show X ≤ H from le_sup_left)).symm
    _ = (pPrimeCore 2 H).map H.subtype := congrArg (fun K => K.map H.subtype) he

/-- The local S₃ marking gives a genuine isomorphism with the source L₂(2). -/
noncomputable def projectiveModel : ↥(⁅fittingSubgroup G, A⁆ ⊔ A) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  d.model.trans ((Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm.trans
    Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two)

end MinimalFittingPlane

/-- A completed decomposition can be presented with the source's actual
projective special linear groups in place of symmetric groups. -/
noncomputable def Decomposition.projectiveFactorModel (d : Decomposition ρ)
    (i : Fin d.count) : d.factor i ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  (d.factorModel i).trans ((Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm.trans
    Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two)

end CFSG.Quasithin.ChapterB.FittingStructure
