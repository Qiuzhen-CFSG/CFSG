module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.MaximalLocal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.NativeLinearFive
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.MathieuTwelveSections
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.FullSylowExclusions

/-!
# Normal unitary residuals in the native J₄ maximal two-locals

The actual four-local catalogue has no normal subgroup with full two-core
quotient U₃(3). In the first involution centralizer a simple U₃(3) section
survives the solvable kernel of the action on M₂₂, contradicting the three-part
of |Aut(M₂₂)|. The linear-five and symmetric-linear rows have insufficient
three-part as well. In the Mathieu row, normality identifies the nontrivial
core quotient with M₂₄, whose order differs from 6048.

The catalogue remains an explicit input at this Theory boundary. Its proved
source-layer producer is applied in Chapter13's `TerminalJanko` module.
All conjugates use actual subgroup isomorphisms and full intrinsic two-cores.

Source: Aschbacher--Smith 4.4.3, maximal-local inspection on printed p.622;
Kleidman--Wilson (1988), §2, pp.488--493. The imported native matrix and
quotient results retain their ATLAS attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.UnitaryNormalResidual
open Janko4.LocalStructure Janko4.InvolutionCentralizers Sporadic.Mathieu
open Janko4.LocalStructure.ElementaryNormalizerCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
set_option backward.isDefEq.respectTransparency true
abbrev U := commutator (Atlas.G2.Model (ZMod 2))

private theorem unitary_nonsolvable : ¬ Group.IsSolvable U := by
  let := Atlas.G2.isSimple_commutator_binary
  intro hs
  let : CommGroup U := { (inferInstance : Group U) with
    mul_comm := IsSimpleGroup.comm_iff_isSolvable.mpr hs }
  have hp := IsSimpleGroup.prime_card (α := U)
  rw [Atlas.G2.LieAutomorphismExtensions.card_binaryDerived] at hp
  norm_num at hp

private theorem first_action_kernel_solvable :
    Group.IsSolvable First.QuotientExtension.centralizerMathieuAction.ker := by
  open First.QuotientExtension in
    rw [centralizerMathieuAction_ker]
    let : Group.IsNilpotent (Q.subgroupOf R) :=
      (pCore_isPGroup.comap_subtype (p := 2) (G := First.centralizer)).isNilpotent
    let : Group.IsSolvable (R ⧸ Q.subgroupOf R) :=
      Group.isSolvable_of_isSolvable_injective
        (f := RQuotientEquivC3.toMonoidHom) RQuotientEquivC3.injective
    exact (Group.isSolvable_iff_subgroup_quotient (Q.subgroupOf R)).mpr
      ⟨inferInstance,inferInstance⟩

/-- The solvable kernel in the actual first involution centralizer cannot
supply the third factor of three in a simple U₃(3) section. -/
theorem first_centralizer_no_unitary_section
    (B : Subgroup First.centralizer) (f : B →* U) (hf : Function.Surjective f) : False := by
  let := Atlas.G2.isSimple_commutator_binary
  let a := First.QuotientExtension.centralizerMathieuAction
  let : Group.IsSolvable a.ker := first_action_kernel_solvable
  obtain ⟨W,g,hg⟩ := simple_section_quotient_of_solvable_kernel unitary_nonsolvable a.ker B f hf
  have hd := (card_dvd_of_surjective g hg).trans W.card_subgroup_dvd_card
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange a).toEquiv] at hd
  have hcard : Nat.card (MulAut.innerSubgroup M22) = Nat.card M22 :=
    (Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)).toEquiv).symm
  have haut : Nat.card (MulAut M22) ∣ Nat.card M22 * 2 := by
    rw [←(MulAut.innerSubgroup M22).card_mul_index,hcard]
    exact Nat.mul_dvd_mul_left _ M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two
  have hbad := (hd.trans a.range.card_subgroup_dvd_card).trans haut
  rw [Atlas.G2.LieAutomorphismExtensions.card_binaryDerived,m22_order] at hbad
  norm_num at hbad

private theorem max2_no_unitary_section
    (B : Subgroup Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.sourceSubgroup)
    (b : B ⧸ pCore 2 B ≃* U) : False := by
  open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData in
    let c : sourceSubgroup ≃* First.centralizer :=
      ((MulAut.conj h⁻¹).subgroupMap sourceSubgroup).trans
        (MulEquiv.subgroupCongr NativeCoverTransport.sourceSubgroup_map_conj_firstCentralizer)
    let d := c.subgroupMap B
    let f := b.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 B)).comp d.symm.toMonoidHom)
    exact first_centralizer_no_unitary_section (B.map c.toMonoidHom) f
      (b.surjective.comp ((QuotientGroup.mk'_surjective _).comp d.symm.surjective))

private theorem max4_no_normal_unitary
    (B : Subgroup SymmetricLinear.max4Subgroup) [B.Normal]
    (b : B ⧸ pCore 2 B ≃* U) : False := by
  have hd : Nat.card (B ⧸ pCore 2 B) ∣
      Nat.card (SymmetricLinear.max4Subgroup ⧸ pCore 2 SymmetricLinear.max4Subgroup) := by
    rw [Nat.card_congr (coreQuotientEquivImage 2 B).toEquiv]
    exact card_subgroup_dvd_card _
  rw [Nat.card_congr b.toEquiv,Atlas.G2.LieAutomorphismExtensions.card_binaryDerived,
    Nat.card_congr SymmetricLinear.max4QuotientEquiv.toEquiv,
    SymmetricLinear.quotientModel_card] at hd
  norm_num at hd

private theorem normal_image_quotient {M X : Type*} [Group M] [Group X]
    (c : M ≃* X) (B : Subgroup M) [B.Normal] (b : B ⧸ pCore 2 B ≃* U) :
    ∃ B' : Subgroup X, B'.Normal ∧ Nonempty (B' ⧸ pCore 2 B' ≃* U) := by
  let B' := B.map c.toMonoidHom
  let : B'.Normal := Normal.map inferInstance c.toMonoidHom c.surjective
  let d : B ≃* B' := c.subgroupMap B
  let q : B' ⧸ pCore 2 B' ≃* B ⧸ pCore 2 B :=
    QuotientGroup.congr _ _ d.symm (pCore_map_iso 2 d.symm)
  exact ⟨B',inferInstance,⟨q.trans b⟩⟩

/-- The actual four-local catalogue excludes a normal U₃(3) residual in every
maximal two-local. Each conjugate is transported through its literal subgroup
isomorphism, and the quotient always uses the full intrinsic two-core. -/
theorem maximal_twoLocal_no_normal_unitary
    (hcover : LargeCenterRadicals.MaximalTwoLocalCover)
    (M : Subgroup Janko4.Model) (hM : IsMaximalTwoLocal M)
    (B : Subgroup M) [B.Normal] (b : B ⧸ pCore 2 B ≃* U) : False := by
  obtain ⟨g,hg | hg | hg | hg⟩ := hcover M hM
  all_goals
    let c := (MulEquiv.subgroupCongr hg).trans ((MulAut.conj g).subgroupMap _).symm
    obtain ⟨B',hn,⟨b'⟩⟩ := normal_image_quotient c B b
    let := hn
  · have e : max1 ⧸ pCore 2 max1 ≃* M24 :=
      (QuotientGroup.quotientMulEquivOfEq (localKernel_eq_twoCore _ _).symm).trans
        (localQuotientEquivM24 _ _)
    exact LargeCenterRadicals.unitary_normal_residual_quotients_excluded B' b'
      (Or.inr (Or.inl ⟨e⟩))
  · exact max2_no_unitary_section B' b'
  · exact LargeCenterRadicals.LinearFiveLocal.unitary_residual_not_embed_linearFive b'
      LinearFive.intrinsicNormalizerQuotient B'.subtype B'.subtype_injective
  · exact @max4_no_normal_unitary B' hn b'
end Janko4.LocalStructure.UnitaryNormalResidual
