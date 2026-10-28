module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Products

/-!
# Comparing the M₁₂ rows

Assume the component quotient is the actual M₁₂ model and supply precisely
its involution table from 16.1.5(4). The outer row has A₅ two-residual.
Containment in the inner residual, together with the central-kernel
solvability equivalence, excludes the solvable quaternion-extension row.
The remaining inner product row also has A₅ residual, giving both actual
central-image equivalences required by the reverse-Δ₀ argument.

This is the M₁₂ branch of the comparison, not a proof that every contrary
configuration has M₁₂ quotient. The remaining family exclusions belong to
the enclosing comparison. Source: Aschbacher–Smith, combined manuscript
(1 March 2004), 16.1.5(4) and proof of 16.4.11(2), printed pp.1171 and 1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu
open OtherPreliminaries.Mathieu
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

private noncomputable def residualCongr {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) : pResidual 2 H ≃* pResidual 2 K :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_pResidual 2 e))

/-- Nonsolvability of the outer image forces nonsolvability of the inner
image, even when the two component centers are different. -/
theorem nonsolvable_inner_of_outer (d : Contrary T z L g R r)
    (hout : ¬ Group.IsSolvable (centralImage (L.conjBy g) (residual (L.conjBy g) z))) :
    ¬ Group.IsSolvable (centralImage L (residual L r)) := by
  intro hin
  let : Group.IsSolvable (residual L r) :=
    (centralImage_solvable_iff ((residual_le L r).trans inf_le_left)).mp hin
  let : Group.IsSolvable (residual (L.conjBy g) z) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective d.residual_normal.1)
  exact hout ((centralImage_solvable_iff
    ((residual_le (L.conjBy g) z).trans inf_le_left)).mpr inferInstance)

/-- The genuine M₁₂ table and the ambient containment select both A₅ rows.
Only the earlier table and the component identification are inputs. -/
theorem m12_comparison_of_table (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* M12)
    (table : ∀ a : MulAut M12, orderOf a = 2 → M12InvolutionAlternative a) :
    M12Comparison L (L.conjBy g) r z := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let ec : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  let : IsQuasisimple (L.conjBy g) := IsQuasisimple.of_mulEquiv ec
  let eM : ((L.conjBy g) ⧸ center (L.conjBy g)) ≃* M12 :=
    (centralQuotientCongr ec).symm.trans e
  let hi := d.setup.sylow_normalizes (d.setup.le_sylow d.mem)
  let a := MulAut.centralQuotientAction e (action hi)
  let b := MulAut.centralQuotientAction eM (action d.z_normalizes)
  have ha : orderOf a = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans d.inner_action_order
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction eM)
      (MulAut.centralQuotientAction_injective eM) _).trans d.outer_action_order
  have hia : ∃ x : M12, a = MulAut.conj x :=
    (MulAut.centralQuotientAction_inner_iff e (action hi)).mpr d.inner_action
  have hob : ¬ ∃ x : M12, b = MulAut.conj x := fun h =>
    d.outer_action ((MulAut.centralQuotientAction_inner_iff eM _).mp h)
  have hbo : Nonempty (b.fixedSubgroup ≃* OtherPreliminaries.Mathieu.C2 ×
      OtherPreliminaries.Mathieu.A5) := by
    rcases table b hb with ⟨hbi, _⟩ | ⟨_, hbo⟩
    · exact (hob hbi).elim
    · exact hbo
  obtain ⟨ebo⟩ := hbo
  let eo : centralImage (L.conjBy g) (residual (L.conjBy g) z) ≃* ReverseDelta.A5 :=
    (centralImageModelEquiv (conjugate_oddCore d) eM d.z_normalizes).trans
      ((residualCongr ebo).trans outerProductResidualEquiv)
  have hnot : ¬ Group.IsSolvable
      (centralImage (L.conjBy g) (residual (L.conjBy g) z)) := by
    intro hsol
    let := hsol
    let : Group.IsPerfect ReverseDelta.A5 :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable ReverseDelta.A5
      (Group.isSolvable_of_surjective (f := eo.toMonoidHom) eo.surjective)
  have hai : Nonempty (a.fixedSubgroup ≃* InnerCentralizerModel) := by
    rcases table a ha with ⟨_, hq | hp⟩ | ⟨hoa, _⟩
    · let : Group.IsSolvable a.fixedSubgroup := quaternionExtension_solvable hq
      have hsol : Group.IsSolvable (centralImage L (residual L r)) :=
        Group.isSolvable_of_surjective
          (f := (centralImageModelEquiv (component_oddCore d) e hi).symm.toMonoidHom)
          (centralImageModelEquiv (component_oddCore d) e hi).symm.surjective
      exact (nonsolvable_inner_of_outer d hnot hsol).elim
    · exact hp
    · exact (hoa hia).elim
  obtain ⟨eai⟩ := hai
  exact ⟨⟨e⟩, ⟨(centralImageModelEquiv (component_oddCore d) e hi).trans
    ((residualCongr eai).trans innerProductResidualEquiv)⟩, ⟨eo⟩⟩

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison
