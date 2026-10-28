module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionNormalSupport
public import Theory.Representation.BinaryOffender.FixedSpaceFaithfulness
public import Theory.Representation.Suzuki.ExchangedDisplacement
public import Theory.Representation.BinaryOffender.RestrictedConstituent

/-!
# Faithful Suzuki support on the actor-centralizer fixed space

For the literal exchanged support X, Thompson A×B puts the pointwise kernel
on C_U(C_A(X)) inside O₂(X). Normality and the original trivial two-core kill
that kernel. The reduced actor kernel is therefore exactly C_A(X), and the
Suzuki automorphism bound gives rank at most 2r+2. D.2.5 retains the cubic
bound on this faithful pair action; D.2.7 makes it strict when the removed
centralizer is nontrivial. Full movement and ambient irreducibility are not
assumed.

The actual chosen-seed application is SeedAlternativesMovedExhaustionSuzukiFixedSpace.
The remaining small-action Suzuki exclusion, FF branches and Source325
assembly belong to qt-baumann-fsu.
Source: Aschbacher--Smith A.1.18 and D.3.9(2), printed pp.27,200--201;
application 3.2.5, p.580, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Thompson A×B retains a two-core-free support on the literal fixed space. -/
private theorem fixedSpace_support_kernel_eq_bot
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (X B : Subgroup H) (hB : IsPGroup 2 B) (hc : ⁅X,B⁆ = ⊥)
    (hcore : pCore 2 X = ⊥) :
    subspaceKernel ρ (fixedSpace ρ B) X = ⊥ := by
  let : Finite E := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative E) := BinaryGroupAction.elementary
  let : FaithfulSMul H (Multiplicative E) := BinaryGroupAction.faithful ρ hf
  have hb := thompson_fixedPoints_kernel_le_pCore (G := Multiplicative E) X B
    (IsElementaryAbelian.isPGroup 2 (Multiplicative E)) hB hc
  apply bot_unique
  intro x hx
  have hm : (⟨x,hx.1⟩ : X) ∈ fixingSubgroup X
      (FixedPoints.subgroup B (Multiplicative E) : Set (Multiplicative E)) := by
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact congrArg Multiplicative.ofAdd (hx.2 v.toAdd hv)
  exact congrArg Subtype.val (hcore.le (hb hm))

/-- The actual exchanged support remains faithful after removing its actor centralizer. -/
theorem exchanged_support_fixedSpace_reduction
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (hcore : pCore 2 H = ⊥) (J A : Subgroup H)
    (hindex : (normalizer (J : Set H)).index = 2)
    (a : H) (ha : a ∈ A) (han : a ∉ normalizer (J : Set H))
    (horbit : componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom)
    (hA : A ∈ CFSG.Quasithin.ChapterD.QhatStar ρ)
    (r : ℕ) (hr : 0 < r) (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :
    let X := componentOrbit J A
    let B := A ⊓ centralizer (X : Set H)
    let W := fixedSpace ρ B
    X.Normal ∧
      subspaceKernel ρ W X = ⊥ ∧
      (∃ hXW : X ≤ subspaceStabilizer ρ W,
        Function.Injective (subgroupActionHom ρ W X hXW)) ∧
      subspaceKernel ρ W A = B ∧
      rank (restrictedSubgroup ρ W A) ≤ 2*r+2 ∧
      restrictedSubgroup ρ W A ∈ CFSG.Quasithin.ChapterD.Qhat
        (subspaceImageRepresentation ρ W) ∧
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) ≤ 2*(2*r+2) ∧
      (B ≠ ⊥ → actionRatio (subspaceImageRepresentation ρ W)
        (restrictedSubgroup ρ W A) < cubicRatio ρ) := by
  intro X B W
  let : X.Normal := by
    dsimp only [X]
    rw [horbit]
    exact sup_conjugate_normal_of_normalizer_index_two J hindex a han
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    (inclusion (show B ≤ A from inf_le_left)) (inclusion_injective _)
  have hxcore : pCore 2 X = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : X.Normal).isSubnormal,hcore]
    exact (MonoidHom.ker_eq_bot_iff X.subtype).mpr X.subtype_injective
  have hc : ⁅X,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (show B ≤ centralizer (X : Set H) from inf_le_right))
  have hker := fixedSpace_support_kernel_eq_bot ρ hf X B
    (IsElementaryAbelian.isPGroup 2 B) hc hxcore
  have hXW : X ≤ subspaceStabilizer ρ W :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ X B hc
  have hfaith := (subgroupActionHom_injective_iff ρ W X hXW).mpr hker
  have hρX : Function.Injective (invariantSubspace ρ X W hXW).toRepresentation := by
    intro x y he
    apply hfaith
    apply subspaceImageRepresentation_injective ρ W
    exact he
  have hkA : subspaceKernel ρ W A = B := by
    apply le_antisymm
    · exact subspaceKernel_le_centralizer_of_faithful ρ X A W hXW hρX
    · exact subactor_le_fixedSpace_kernel ρ (show B ≤ A from inf_le_left)
  have hn : ¬ W ≤ fixedSpace ρ A := by
    intro hh
    have hab : a ∈ B := hkA ▸ (show a ∈ subspaceKernel ρ W A from
      ⟨ha,fun v hv => hh hv ⟨a,ha⟩⟩)
    exact han ((Subgroup.centralizer_le_normalizer _) ((centralizer_le
      (show (J : Set H) ⊆ X from le_componentOrbit J A)) hab.2))
  have hAW : A ≤ subspaceStabilizer ρ W :=
    fixedSpace_subactor_stabilized ρ hA.1.2.1 inf_le_left
  have hbound := CFSG.Quasithin.ChapterD.RPlusBound.restricted ρ
    (show A ∈ CFSG.Quasithin.ChapterD.RPlusBound ρ 2 from
      ⟨⟨hA.1.2.1,hA.1.2.2.2.le.trans hA.1.1⟩,
        CFSG.Quasithin.ChapterD.QhatStar.mem_RPlus ρ hA⟩) W hAW hn
  have hQ : restrictedSubgroup ρ W A ∈ CFSG.Quasithin.ChapterD.Qhat
      (subspaceImageRepresentation ρ W) :=
    ⟨hbound.1,CFSG.Quasithin.ChapterD.isCubic_restrictedSubgroup ρ W hA.1.2.2.1,hbound.2⟩
  have hsum := rank_subspaceKernel_add_image ρ W A hAW (IsElementaryAbelian.isPGroup 2 A)
  rw [hkA] at hsum
  have hRank := Representation.Suzuki.exchanged_actor_rank_le J A hindex r hr e
  change rank A ≤ rank B + (2*r+1) + 1 at hRank
  have hrank : rank (restrictedSubgroup ρ W A) ≤ 2*r+2 := by omega
  have hcod := (actionRatio_le_nat_iff _ hbound.1 2).mp hbound.2
  refine ⟨inferInstance,hker,⟨hXW,hfaith⟩,hkA,hrank,hQ,by omega,?_⟩
  intro hB
  exact (CFSG.Quasithin.ChapterD.QhatStar.fixedSpace_ratio_drop ρ hA
    (show B ≤ A from inf_le_left) hB (fun he => hn ((subspaceCommutator_eq_bot_iff ρ W A).mp he))).2
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
