module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Basic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.Obstruction
public import GorensteinWalter.PSL2PerfectOfCard
public import GorensteinWalter.PSL2Center

/-!
# Offender reduction and low-row exclusions in the component branch

If the ambient generalized Fitting subgroup is quasisimple, the literal
normal offender subgroup cannot have any of the nonquasisimple B.5.6
configurations. The existing product obstructions apply to its original
restricted action, so the surviving conclusion retains all six B.5.1
clauses, including their module and action witnesses.

F.6.18(2) is solvable even for the nonsplit extraspecial extension. In
F.6.18(3), the prime-field parameter makes the PSL₂ factor quasisimple.
Its normality inside the actual two-residual makes it a component. If
ambient F* were quasisimple, it would equal that factor, forcing the
separate centralizing C₃ into it by self-centralization, a contradiction.
No rank bound, ambient normality of a direct factor, or splitting is assumed.

The source classifications remain explicit premises; these are their
structural reductions for the terminal comparison.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.1/B.5.6, printed pp.99–105; F.6.17–18, printed pp.309–310;
final proof of 15.3.1, printed p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

namespace ComponentRows.OffenderReduction

private theorem quasisimple_not_solvable {D : Type*} [Group D]
    (h : IsQuasisimple D) : ¬ Group.IsSolvable D := by
  let _ := h
  let _ := h.simple
  let _ : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact Group.IsPerfect.not_isSolvable D

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let _ : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))

variable {D : Type*} [Group D] [Finite D]

/-- Both actual models in row (2) are solvable; no complement to the
extraspecial kernel is needed. -/
theorem row_two_solvable
    (h : Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup D, ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty ((D ⧸ N) ≃* FSource.E4)) : Group.IsSolvable D := by
  rcases h with hm | ⟨N, hn, he, _, _, ⟨e⟩⟩
  · obtain ⟨e⟩ := hm
    let _ := symmetricThree_solvable
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · let _ := hn
    let _ := he
    let _ : Group.IsNilpotent N := (IsExtraspecial.isPGroup 3 N).isNilpotent
    let _ : Group.IsSolvable (D ⧸ N) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩

/-- Row (2) is impossible above a quasisimple generalized Fitting subgroup. -/
theorem not_row_two (hL : IsQuasisimple (generalizedFitting D))
    (h : Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup D, ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty ((D ⧸ N) ≃* FSource.E4)) : False := by
  let _ := row_two_solvable h
  exact quasisimple_not_solvable hL inferInstance

omit [Finite D] in
private theorem pair_commute {A B : Subgroup D} (f : (A × B) →* D)
    (hf : ∀ a b, f (a,b) = (a : D) * (b : D)) : ⁅A,B⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha
  apply mem_centralizer_iff.mpr
  intro b hb
  have he : f (⟨a,ha⟩,1) * f (1,⟨b,hb⟩) = f (1,⟨b,hb⟩) * f (⟨a,ha⟩,1) := by
    rw [← map_mul, ← map_mul]
    simp
  simpa [hf] using he.symm

omit [Finite D] in
private theorem pair_disjoint {A B : Subgroup D} (f : (A × B) →* D)
    (hi : Function.Injective f) (hf : ∀ a b, f (a,b) = (a : D) * (b : D)) :
    Disjoint A B := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro x hx
  have he : f (⟨x,hx.1⟩,1) = f (1,⟨x,hx.2⟩) := by simp [hf]
  exact congrArg (fun y : A × B => (y.1 : D)) (hi he)

omit [Finite D] in
/-- The prime-field parameter in row (3) makes its actual PSL₂ factor
quasisimple. -/
theorem productRow_first_quasisimple {S : Sylow 2 D} (r : FSource.ProductRow S) :
    IsQuasisimple r.first := by
  have hcard : Nat.card r.field.Carrier = r.field.prime := by
    rw [r.field.card, r.degree, pow_one]
  have hlarge : 4 ≤ Nat.card r.field.Carrier := by
    have hc := r.congruence
    omega
  let _ := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let _ : IsQuasisimple PSL(2,r.field.Carrier) :=
    { toIsPerfect := GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by omega)
      simple := ((QuotientGroup.quotientMulEquivOfEq
        (GorensteinWalter.psl2_center_eq_bot r.field.Carrier)).trans
          QuotientGroup.quotientBot).isSimpleGroup }
  exact IsQuasisimple.of_mulEquiv r.firstEquiv.symm

omit [Finite D] in
/-- The factor is subnormal through the literal two-residual product;
no ambient normality of an arbitrary direct factor is assumed. -/
theorem productRow_first_subnormal {S : Sylow 2 D} (r : FSource.ProductRow S) :
    r.first.IsSubnormal := by
  let f : (r.first × r.second) →* D :=
    (r.first ⊔ r.second).subtype.comp r.product.toMonoidHom
  have hc : ⁅r.first,r.second⁆ = ⊥ := pair_commute f r.product_apply
  have hn : (r.first.subgroupOf (r.first ⊔ r.second)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    apply sup_le r.first.le_normalizer
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (by simpa [commutator_comm] using hc)).trans (Subgroup.centralizer_le_normalizer _)
  have hN : (r.first ⊔ r.second).Normal := r.residual ▸ inferInstance
  exact Subgroup.IsSubnormal.trans le_sup_left hn.isSubnormal hN.isSubnormal

/-- The disjoint cubic factor centralizes the PSL₂ component, contradicting
self-centralization if the ambient F* were quasisimple. -/
theorem not_productRow (hL : IsQuasisimple (generalizedFitting D))
    {S : Sylow 2 D} (r : FSource.ProductRow S) : False := by
  have hfirst : IsComponent D r.first :=
    ⟨productRow_first_subnormal r, productRow_first_quasisimple r⟩
  have hcomp : IsComponent D (generalizedFitting D) :=
    ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hL⟩
  have he : r.first = generalizedFitting D :=
    hfirst.eq_of_le hcomp (component_le_generalizedFitting D _ hfirst)
  let f : (r.first × r.second) →* D :=
    (r.first ⊔ r.second).subtype.comp r.product.toMonoidHom
  have hc : ⁅r.first,r.second⁆ = ⊥ := pair_commute f r.product_apply
  have hd : Disjoint r.first r.second := pair_disjoint f
    (Subtype.val_injective.comp r.product.injective) r.product_apply
  have hb : r.second ≤ r.first := by
    have hh : r.second ≤ centralizer (r.first : Set D) :=
      commutator_eq_bot_iff_le_centralizer.mp (by simpa [commutator_comm] using hc)
    rw [he] at hh ⊢
    exact hh.trans ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hz : r.second = ⊥ := le_bot_iff.mp
    ((le_inf hb le_rfl).trans (disjoint_iff.mp hd).le)
  let _ : Nontrivial r.second := r.secondEquiv.symm.injective.nontrivial
  exact (nontrivial_iff_ne_bot _).mp inferInstance hz

end ComponentRows.OffenderReduction

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- Eliminate every other B.5.6 constructor while preserving the complete
B.5.1 action witness on the actual offender group. -/
theorem offender_quasisimple_source_of_sourceAlternative
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (hB : FFAlternatives.SourceAlternative d.offenderAction) :
    Nonempty (FFAlternatives.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) := by
  cases hB with
  | trivial h =>
    let _ := h
    apply (d.offender_ne_bot ?_).elim
    apply le_bot_iff.mp
    intro x hx
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subsingleton.elim (⟨x,hx⟩ : d.offenderGroup) 1))
  | quasisimple _ c => exact ⟨c⟩
  | symmetricThree c =>
    exact (d.thompson_image_not_symmetricThree hL (d.thompsonEquivSymmetricThree c.equiv)).elim
  | twoFactors c =>
    exact (ProductComparison.sourceTwoFactor_not_quasisimple
      (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) c hL).elim
  | outerSixThree c =>
    exact (ProductComparison.outerSixThree_not_quasisimple
      (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) c hL).elim
  | hyperplane c =>
    exact (ProductComparison.hyperplane_not_quasisimple
      (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) c hL).elim

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
