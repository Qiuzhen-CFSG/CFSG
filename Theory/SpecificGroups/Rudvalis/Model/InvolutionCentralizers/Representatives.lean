module

public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Shapes
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers
public import Theory.SpecificGroups.Rudvalis.Model.ThreeConjugates.Fusion
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Full centralizer transport for the two Rudvalis involution classes

The checked involution forest covers every actual involution by a or b².
The checked conjugator from the max6 marker to b² identifies its full
centralizer with max6. Restriction of conjugation transports that equality,
the actual two-core order, and the five-letter quotient to the whole class.

The E₃₂/E₆₄ refinement and the structure of C(a) are separate obligations;
this module does not infer either from orders or from the class labels.
Source: Aschbacher–Smith, 16.1.5(11), printed p.1172; GLS3 Table 5.3r.
The imported certificates retain the original ATLAS words and conventions.
-/

@[expose] public section

open Subgroup
namespace Rudvalis.InvolutionCentralizers
open Theory.GroupTheory.CentralizerSmallKernelTransport
open SylowOvergroups

/-- Conjugacy restricts to an equivalence of the full literal centralizers. -/
noncomputable def centralizerEquivOfIsConj {s t : Model} (h : IsConj s t) :
    Centralizer s ≃* Centralizer t :=
  let g := Classical.choose (isConj_iff.mp h)
  (centralizerEquiv (MulAut.conj g) s).trans
    (MulEquiv.subgroupCongr (congrArg (fun z : Model => Centralizer z)
      (Classical.choose_spec (isConj_iff.mp h))))

/-- The full centralizer of b² is the previously certified max6 subgroup. -/
noncomputable def squareCentralizerEquiv : Centralizer (b ^ 2) ≃* max6 :=
  (centralizerEquivOfIsConj (isConj_iff.mpr
    ⟨LowCentralizers.squareConjugator, LowCentralizers.squareConjugator_alignment⟩)).symm.trans
      (MulEquiv.subgroupCongr LowCentralizers.max6_eq_centralizer.symm)

/-- Every member of the b² class has the actual max6 centralizer. -/
noncomputable def firstCentralizerEquiv {t : Model} (h : IsConj t (b ^ 2)) :
    Centralizer t ≃* max6 :=
  (centralizerEquivOfIsConj h).trans squareCentralizerEquiv

/-- Every involution centralizer is transported from one of the two actual representatives. -/
theorem centralizer_representatives (t : Model) (ht : orderOf t = 2) :
    (IsConj t (b ^ 2) ∧ Nonempty (Centralizer t ≃* max6)) ∨
      (IsConj t a ∧ Nonempty (Centralizer t ≃* Centralizer a)) := by
  rcases involution_isConj_a_or_b_sq t ht with h | h
  · exact Or.inr ⟨h, ⟨centralizerEquivOfIsConj h⟩⟩
  · exact Or.inl ⟨h, ⟨firstCentralizerEquiv h⟩⟩

/-- The quotient by the actual two-core in the b² class is S₅. -/
noncomputable def firstQuotientEquiv {t : Model} (h : IsConj t (b ^ 2)) :
    (Centralizer t ⧸ pCore 2 (Centralizer t)) ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.congr _ _ (firstCentralizerEquiv h)
    (pCore_map_iso 2 (firstCentralizerEquiv h))).trans
      CoreQuotients.max6FiveQuotientEquiv

/-- The intrinsic two-core of every b²-class centralizer has order 2048. -/
theorem first_core_card {t : Model} (h : IsConj t (b ^ 2)) :
    Nat.card (pCore 2 (Centralizer t)) = 2048 := by
  let e := firstCentralizerEquiv h
  have he := Nat.card_congr (e.subgroupMap (pCore 2 (Centralizer t))).toEquiv
  change Nat.card (pCore 2 (Centralizer t)) =
    Nat.card ((pCore 2 (Centralizer t)).map e.toMonoidHom) at he
  rw [pCore_map_iso] at he
  rw [he, ← CoreQuotients.max6FiveAction_ker]
  exact CoreQuotients.max6FiveAction_kernel_card

/-- The full centralizer of every b²-class involution has order 245760. -/
theorem first_centralizer_card {t : Model} (h : IsConj t (b ^ 2)) :
    Nat.card (Centralizer t) = 245760 :=
  (Nat.card_congr (firstCentralizerEquiv h).toEquiv).trans max6_card

end Rudvalis.InvolutionCentralizers
