module

public import Theory.GroupTheory.QuasisimpleGraphQuotientLifting
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.LinearCoverAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.LinearGraph

/-!
# An actual graph involution for the special-linear source cover

Pass to the centralizer quotient, whose generalized Fitting subgroup is
the simple central quotient of the original component. The proved linear
automorphism theorem supplies an outside graph involution there. Its odd
kernel permits an involution lift in the original group. The newly marked
scalar-cover theorem and perfect-cover uniqueness recover inverse transpose
on the actual special-linear component, together with ambient generation.

Source: Aschbacher--Smith F.6.18(11), printed p.310, and I.1.1--I.1.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open QuasisimpleGraphQuotientLifting
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H] [Field F] [Finite F]
theorem exists_special_linear_graph_involution (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G))
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hproper : generalizedFitting G ≠ ⊤) (hz : center (generalizedFitting G) ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (eK : generalizedFitting G ⧸ center (generalizedFitting G) ≃* PSL(3,F)) :
    ∃ t : G, orderOf t = 2 ∧ t ∉ generalizedFitting G ∧
      generalizedFitting G ⊔ zpowers t = ⊤ ∧
      ∃ j : generalizedFitting G ≃* SL(3,F),
        ∀ x : generalizedFitting G,
          j (MulAut.conjNormal t x) = Matrix.PSL3.OuterSolvable.graphSL F (j x) := by
  let K := generalizedFitting G
  let : IsQuasisimple K := hK.2
  have hq : IsPGroup 2 (G ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K (T : Subgroup G) T.isPGroup' hgen
  let Q := CentralizerQuotient K
  let q := centralizerQuotientMap K
  let S := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup (generalizedFitting Q) := quotient_fitting_simple K hq
  let eQ := (fittingEquiv K hq).symm.trans eK
  obtain ⟨b, hb2, hbout, hbgen, a, ha⟩ :=
    exists_projective_linear_graph_involution S
      (quotient_fitting_sup_sylow K hq T hgen)
      (quotient_fitting_proper K hq rfl hproper) hp ho hF eQ
  obtain ⟨t, htq, ht2, htout, htgen⟩ :=
    exists_lift_involution K hq rfl (component_center_odd_of_primeToThree_quotient eG hK)
      b hb2 hbout hbgen
  let eNew := (fittingEquiv K hq).trans a
  have hNew : ∀ x : K, eNew (QuotientGroup.mk' (center K) (MulAut.conjNormal t x)) =
      Matrix.PSL3.OuterSolvable.graph F (eNew (QuotientGroup.mk' (center K) x)) := by
    intro x
    change a (fittingMap K hq (MulAut.conjNormal t x)) =
      Matrix.PSL3.OuterSolvable.graph F (a (fittingMap K hq x))
    rw [fittingMap_conj, htq, ha]
  obtain ⟨j, hj⟩ := component_linear_graph_action_of_quotient hK (hF.symm ▸ ho)
    eNew hz (MulAut.conjNormal t) hNew
  exact ⟨t, ht2, htout, htgen, j, hj⟩
end CFSG.Quasithin.ChapterF.SourceAssembly
