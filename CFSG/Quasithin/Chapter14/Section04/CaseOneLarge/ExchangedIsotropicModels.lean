module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulRecognition

/-!
# Carrier recognition for the original isotropic exchanged constituent

The sharp stabilizer degree and non-self-duality exclude the actual carrier
models using the completed small-representation theorems. The remaining
binary PSL3 central quotients are excluded by the original elementary Sylow
actor. Thus the original component is A7, without a recognition premise.
This does not yet identify the whole terminal group or its marked action.

The sieve adapts the checked Section03 exchanged-image proofs to the genuine
G.9 input supplied by ExchangedIsotropic; it uses no rank-two flag hypotheses.
Source: Aschbacher--Smith G.11.6, printed p.366, and 14.4.2, pp.1006--1007;
refs/quasithin.pdf.
-/

noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropicModels
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open ChapterG.Section07

private structure SharpAction {D U : Type*} [Group D] [Finite D]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (A H : Subgroup D) : Prop where
  hypothesis : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
    ρ A H H (finrank (ZMod 2) U - 2)
  dimension_gt_two : 2 < finrank (ZMod 2) U
  not_selfDual : ¬ Nonempty (Representation.Equiv (ρ.comp H.subtype) (Representation.dual (ρ.comp H.subtype)))
  proper : ¬ Function.Surjective (Representation.asGroupHom (ρ.comp H.subtype))

namespace SharpAction
variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {A J : Subgroup D} (s : SharpAction ρ A J)
include s

private theorem rank_bound : finrank (ZMod 2) U ≤ primeRank 2 (MulAut J) + 2 := by
  let : J.Normal := s.hypothesis.normal_H
  let : IsIrreducible (ρ.comp J.subtype) := s.hypothesis.irreducible
  have hr := s.hypothesis.toSetup.rank_le_automorphisms (L := J) (by
    rw [normalizer_eq_top]
    exact le_top)
  have hd := s.dimension_gt_two
  omega

private theorem quotient_rank_bound : finrank (ZMod 2) U ≤
    primeRank 2 (MulAut (J ⧸ center J)) + 2 := by
  let : IsQuasisimple J := s.hypothesis.component.2
  exact s.rank_bound.trans (Nat.add_le_add_right (automorphism_primeRank_le_quotient_center 2) 2)

private theorem faithful : Function.Injective (ρ.comp J.subtype) :=
  s.hypothesis.faithful.comp J.subtype_injective

attribute [local instance] ZMod.algebra
local instance hermitianBinaryModule (n : ℕ) [NeZero n] :
    Module (ZMod 2) (OrthogonalFourMinus.FiniteModel.Space n) :=
  Module.compHom _ (algebraMap (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField n))
section Field
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
include s

private theorem image_not_rank_one_natural
    (hq : ChapterG.Section09.Quasiequivalent
      (ρ.comp (J).subtype)
      (SL2.BinarySmall.natural (K := K))) : False := by
  apply s.not_selfDual
  apply ExchangedAction.selfDual_of_quasiequivalent hq
  refine .mk (SL2OrthogonalCover.binarySelfDual (F := K)) ?_
  intro a
  apply LinearMap.ext
  intro w
  exact SL2OrthogonalCover.binarySelfDual_equivariant a w

set_option backward.isDefEq.respectTransparency false in
private theorem image_not_rank_one_hermitian (n : ℕ) [NeZero n]
    (hq : ChapterG.Section09.Quasiequivalent
      (ρ.comp (J).subtype)
      (SL2.BinarySmall.hermitian n)) : False := by
  obtain ⟨e,f,hf⟩ := hq
  obtain ⟨ell,hell⟩ := Module.Projective.exists_dual_eq_one (ZMod 2)
    (show (1 : OrthogonalFourMinus.FiniteModel.fixedField n) ≠ 0 from one_ne_zero)
  have hzform := (OrthogonalFourMinus.FiniteModel.form n).map_zero
  change OrthogonalFourMinus.FiniteModel.determinant n 0 = 0 at hzform
  let q : QuadraticForm (ZMod 2) U := QuadraticMap.ofPolar
    (fun w => ell (OrthogonalFourMinus.FiniteModel.form n (f w)))
    (by intro a w; fin_cases a <;> simp [hzform])
    (by
      intro x y z
      simpa only [QuadraticMap.polar, map_add, map_sub] using
        congrArg ell ((OrthogonalFourMinus.FiniteModel.form n).polar_add_left (f x) (f y) (f z)))
    (by intro a x y; fin_cases a <;> simp [QuadraticMap.polar, hzform])
  have hinv : ∀ a w, q ((ρ.comp (J).subtype) a w) = q w := by
    intro a w
    change ell (OrthogonalFourMinus.FiniteModel.form n (f (ρ a w))) = _
    have hfw := hf a w
    change f (ρ a w) = SL2.BinarySmall.hermitian n (e a) (f w) at hfw
    rw [hfw]
    exact congrArg ell (OrthogonalFourMinus.FiniteModel.form_preserved n (e a) (f w))
  let : IsIrreducible (ρ.comp (J).subtype) := s.hypothesis.irreducible
  have hz := BinaryQuadraticConstituent.quadratic_eq_zero_of_not_self_dual
    (ρ.comp (J).subtype)
    (by have := s.dimension_gt_two; omega) q hinv s.not_selfDual
  let w := (OrthogonalFourMinus.FiniteModel.coordinates n).symm ((1,1),0)
  have hval := congrArg (fun q : QuadraticForm (ZMod 2) U => q (f.symm w)) hz
  change ell (OrthogonalFourMinus.FiniteModel.form n (f (f.symm w))) = 0 at hval
  rw [f.apply_symm_apply] at hval
  have hw : OrthogonalFourMinus.FiniteModel.form n w = 1 := by
    rw [OrthogonalFourMinus.FiniteModel.form_coordinates]
    simp only [one_mul, sub_eq_self]
    apply Subtype.ext
    simp [OrthogonalFourMinus.FiniteModel.norm]
  rw [hw,hell] at hval
  exact one_ne_zero hval

private theorem image_not_binary_rank_one {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : J ≃* SL(2,K)) : False := by
  let H := J
  let σ := (ρ.comp H.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp H.subtype)).mpr s.hypothesis.irreducible
  have hf : Function.Injective σ :=
    s.hypothesis.faithful.comp (H.subtype_injective.comp e.symm.injective)
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hK
  have hd : finrank (ZMod 2) U ≤ n + 2 := by omega
  rcases ChapterG.Section09.DefiningCharacteristic.binary_small_faithful_classification
      σ hf n hn hK (by omega) with hnat | hherm | htriple
  · obtain ⟨a⟩ := hnat.2.2
    apply s.image_not_rank_one_natural (K := K)
    refine ⟨e,a.toLinearEquiv,?_⟩
    intro x w
    have hh := LinearMap.congr_fun (a.toIntertwiningMap.isIntertwining' (e x)) w
    change a.toLinearEquiv (ρ (H.subtype (e.symm (e x))) w) =
      SL2.BinarySmall.natural (e x) (a.toLinearEquiv w) at hh
    change a.toLinearEquiv (ρ (H.subtype x) w) =
      SL2.BinarySmall.natural (e x) (a.toLinearEquiv w)
    simpa only [MulEquiv.symm_apply_apply] using hh
  · obtain ⟨_,_,t,ht⟩ := hherm
    obtain ⟨k,⟨a⟩⟩ := ht
    let : NeZero (finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] (Representation.asModule σ))) := ⟨t.ne'⟩
    apply s.image_not_rank_one_hermitian (finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] (Representation.asModule σ)))
    refine ⟨e.trans (Atlas.fieldEquivSL 2 k),a.toLinearEquiv,?_⟩
    intro x w
    have hh := LinearMap.congr_fun (a.toIntertwiningMap.isIntertwining' (e x)) w
    change a.toLinearEquiv (ρ (H.subtype (e.symm (e x))) w) =
      SL2.BinarySmall.hermitian (finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] (Representation.asModule σ))) ((Matrix.SpecialLinearGroup.map k.toRingHom) (e x))
        (a.toLinearEquiv w) at hh
    change a.toLinearEquiv (ρ (H.subtype x) w) =
      SL2.BinarySmall.hermitian (finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] (Representation.asModule σ))) ((Matrix.SpecialLinearGroup.map k.toRingHom) (e x))
        (a.toLinearEquiv w)
    simpa only [MulEquiv.symm_apply_apply] using hh
  · have h3 := htriple.2.1
    have h8 := htriple.2.2.1
    omega

end Field

private def alternating_six_first_selfDual :
    BinaryAlternatingSix.firstAlternating.Equiv BinaryAlternatingSix.firstAlternating.dual := by
  apply Representation.BinaryCoverSocle.selfDualOfPairing
    BinaryAlternatingSix.firstAlternating Theory.SpecificGroups.SymmetricSix.polarForm
  · apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro w hw
    exact Theory.SpecificGroups.SymmetricSix.polarForm_nondegenerate.1 w
      (fun v => LinearMap.congr_fun hw v)
  · intro a w z
    have hh := Theory.SpecificGroups.SymmetricSix.polarAction_form a.val w
      (BinaryAlternatingSix.firstAlternating a⁻¹ z)
    change Theory.SpecificGroups.SymmetricSix.polarForm
      (BinaryAlternatingSix.firstAlternating a w)
      (BinaryAlternatingSix.firstAlternating a (BinaryAlternatingSix.firstAlternating a⁻¹ z)) =
      Theory.SpecificGroups.SymmetricSix.polarForm w
        (BinaryAlternatingSix.firstAlternating a⁻¹ z) at hh
    rw [Representation.self_inv_apply] at hh
    exact hh

section Field
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
include s

private theorem image_not_symplectic_four_natural [Algebra (ZMod 2) K]
    (hq : ChapterG.Section09.Quasiequivalent
      (ρ.comp (J).subtype)
      (ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.binaryNatural K)) :
    False := by
  apply s.not_selfDual
  apply ExchangedAction.selfDual_of_quasiequivalent hq
  refine .mk (SymplecticFourOrthogonalCover.binarySelfDual (K := K)) ?_
  intro a
  apply LinearMap.ext
  intro w
  exact SymplecticFourOrthogonalCover.binarySelfDual_equivariant a w

private theorem image_not_nonbinary_symplectic_four {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n)
    (e : J ≃*
      commutator (Matrix.symplecticGroup (Fin 2) K)) : False := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let H := J
  let σ := (ρ.comp H.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp H.subtype)).mpr s.hypothesis.irreducible
  have hf : Function.Injective σ :=
    s.hypothesis.faithful.comp (H.subtype_injective.comp e.symm.injective)
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derived_automorphism_rank_le hK hn
  change primeRank 2 (MulAut (commutator (Matrix.symplecticGroup (Fin 2) K))) ≤ 3 * n at hr
  have hd : finrank (ZMod 2) U ≤ 6 * n + 2 := by omega
  have hq := ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.small_quasiequivalent
    hn hK hf hd
  exact s.image_not_symplectic_four_natural
    (ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.quasiequivalent_of_comp_equiv e hq)

omit [CharP K 2] in
private theorem image_not_alternating_six
    (e : J ≃* alternatingGroup (Fin 6)) : False := by
  let H := J
  let σ := (ρ.comp H.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp H.subtype)).mpr s.hypothesis.irreducible
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank
  have hd : finrank (ZMod 2) U ≤ 5 := by omega
  rcases BinaryAlternatingSix.alternating_classify σ with h | h | h | h <;> obtain ⟨a⟩ := h
  · have hh := a.toLinearEquiv.finrank_eq
    have hp := s.dimension_gt_two
    simp only [Module.finrank_self] at hh
    omega
  · apply s.not_selfDual
    apply ExchangedAction.selfDual_of_quasiequivalent (σ := BinaryAlternatingSix.firstAlternating) _
      alternating_six_first_selfDual
    refine ⟨e,a.toLinearEquiv,?_⟩
    intro x w
    have hh := LinearMap.congr_fun (a.toIntertwiningMap.isIntertwining' (e x)) w
    change a.toLinearEquiv (ρ (H.subtype (e.symm (e x))) w) =
      BinaryAlternatingSix.firstAlternating (e x) (a.toLinearEquiv w) at hh
    change a.toLinearEquiv (ρ (H.subtype x) w) =
      BinaryAlternatingSix.firstAlternating (e x) (a.toLinearEquiv w)
    simpa only [MulEquiv.symm_apply_apply] using hh
  · apply s.not_selfDual
    apply ExchangedAction.selfDual_of_quasiequivalent (σ := BinaryAlternatingSix.firstAlternating) _
      alternating_six_first_selfDual
    refine ⟨e.trans BinaryAlternatingSix.alternatingDiagramAut,a.toLinearEquiv,?_⟩
    intro x w
    have hh := LinearMap.congr_fun (a.toIntertwiningMap.isIntertwining' (e x)) w
    change a.toLinearEquiv (ρ (H.subtype (e.symm (e x))) w) =
      BinaryAlternatingSix.firstAlternating (BinaryAlternatingSix.alternatingDiagramAut (e x))
        (a.toLinearEquiv w) at hh
    change a.toLinearEquiv (ρ (H.subtype x) w) =
      BinaryAlternatingSix.firstAlternating (BinaryAlternatingSix.alternatingDiagramAut (e x))
        (a.toLinearEquiv w)
    simpa only [MulEquiv.symm_apply_apply] using hh
  · have hh := a.toLinearEquiv.finrank_eq.trans BinaryAlternatingSix.tensor_finrank
    omega

omit [CharP K 2] in
private theorem image_not_binary_symplectic_four (hK : Nat.card K = 2)
    (e : J ≃*
      commutator (Matrix.symplecticGroup (Fin 2) K)) : False :=
  s.image_not_alternating_six
    (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hK))

private theorem image_not_symplectic_four {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n)
    (e : J ≃*
      commutator (Matrix.symplecticGroup (Fin 2) K)) : False := by
  by_cases hn1 : n = 1
  · exact s.image_not_binary_symplectic_four (by simpa [hn1] using hK) e
  · exact s.image_not_nonbinary_symplectic_four (by omega) hK e

private theorem image_not_nonbinary_g2 {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : J ≃* commutator (Atlas.G2.Model K)) : False := by
  have hq : 2 < Nat.card K := by
    rw [hK]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  let : Group.IsPerfect (Atlas.G2.Model K) := Atlas.G2.isPerfect hq
  let E : J ≃* Atlas.G2.Model K :=
    e.trans ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv)
  let H := J
  let σ := (ρ.comp H.subtype).comp E.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective
      (ρ.comp H.subtype)).mpr s.hypothesis.irreducible
  have hf : Function.Injective σ :=
    s.hypothesis.faithful.comp (H.subtype_injective.comp E.symm.injective)
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr E)] at hu
  have hr := Atlas.G2.EvenTwoRank.source_automorphism_two_rank_le K hn hK
  have hd : finrank (ZMod 2) U ≤ 6 * n + 2 := by omega
  obtain ⟨_,t,l,ht,_,hnt,hdim,hne,hbasic⟩ :=
    ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary.exists_basic_parameters
      σ hn hK hf
  have hp := ChapterG.Section09.DefiningCharacteristic.G2Recognition.small_basic_block_parameters
    l hbasic hne (by omega) ht hnt hdim hd
  omega

private theorem image_not_g2_zmod_two
    (e : J ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := Atlas.G2.binary_derived_automorphism_two_rank_le_three
  have hd : finrank (ZMod 2) U ≤ 5 := by omega
  have hc : Nat.card (J) = 6048 := by
    rw [Nat.card_congr e.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.card_H
  have hi : Function.Injective (ρ.comp (J).subtype) :=
    s.hypothesis.faithful.comp (J).subtype_injective
  have hdiv := Representation.card_dvd_card_GL_of_injective
    (ρ.comp (J).subtype) hi
  rw [hc, Matrix.card_GL_field] at hdiv
  simp only [ZMod.card] at hdiv
  have hd27 := (by decide : 27 ∣ 6048).trans hdiv
  interval_cases h : finrank (ZMod 2) U <;> norm_num [Fin.prod_univ_succ] at hd27

omit [CharP K 2] in
private theorem image_not_binary_g2 (hK : Nat.card K = 2)
    (e : J ≃* commutator (Atlas.G2.Model K)) : False := by
  let a := Atlas.G2.fieldEquiv (Atlas.G2.binaryFieldEquiv hK)
  let f : commutator (Atlas.G2.Model K) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
    (a.subgroupMap _).trans (MulEquiv.subgroupCongr (by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr a.surjective, commutator_def]))
  exact s.image_not_g2_zmod_two (e.trans f)

private theorem image_not_g2 {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2 ^ n)
    (e : J ≃* commutator (Atlas.G2.Model K)) : False := by
  by_cases hn1 : n = 1
  · exact s.image_not_binary_g2 (by simpa [hn1] using hK) e
  · exact s.image_not_nonbinary_g2 (by omega) hK e

end Field

include s

private theorem not_binary_linear_natural_degree {n : ℕ} (hn : 0 < n)
    (e : J ≃* PSL(n, ZMod 2))
    (hd : finrank (ZMod 2) U = n) : False := by
  let f : U ≃ₗ[ZMod 2] _root_.BinaryLinear.OuterCyclic.Space n :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let E : (U →ₗ[ZMod 2] U)ˣ ≃* _root_.BinaryLinear.OuterCyclic.LinearGroup n :=
    (Units.mapEquiv f.conjRingEquiv.toMulEquiv).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
        (_root_.BinaryLinear.OuterCyclic.Space n))
  have hc : Nat.card (U →ₗ[ZMod 2] U)ˣ = Nat.card (J) :=
    (Nat.card_congr E.toEquiv).trans
      (Nat.card_congr (e.trans (_root_.BinaryLinear.OuterCyclic.projectiveEquivLinear hn)).toEquiv).symm
  let : Finite (U →ₗ[ZMod 2] U)ˣ := Finite.of_equiv (J)
    ((e.trans (_root_.BinaryLinear.OuterCyclic.projectiveEquivLinear hn)).trans E.symm).toEquiv
  let r : J →* (U →ₗ[ZMod 2] U)ˣ := (Representation.asGroupHom (ρ.comp J.subtype))
  have hi : Function.Injective r := (fun a b hab => s.faithful (congrArg Units.val hab))
  exact s.proper (hi.bijective_of_nat_card_le hc.le).2

private theorem not_binary_linear_four_equiv
    (e : J ≃* PSL(4, ZMod 2)) : False := by
  let σ := (ρ.comp J.subtype).comp e.symm.toMonoidHom
  have hi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp J.subtype)).mpr s.hypothesis.irreducible
  have hf : Function.Injective σ := s.faithful.comp e.symm.injective
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := _root_.BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
  have hd : finrank (ZMod 2) U ≤ 10 := by omega
  rcases ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.small_modules
      σ hf hi hd with hnat | ⟨a,f,hf⟩
  · exact s.not_binary_linear_natural_degree (by decide) e hnat
  · let q := (ClassicalOrthogonal.formD 3 (ZMod 2)).comp f.toLinearMap
    have hq : ∀ h : J, ∀ v : U, q ((ρ.comp J.subtype) h v) = q v := by
      intro h v
      have hh := hf (e h) v
      change f ((ρ.comp J.subtype) (e.symm (e h)) v) =
        Representation.BinaryLinearRecognition.orthogonalEightAction (a (e h)) (f v) at hh
      rw [e.symm_apply_apply] at hh
      change ClassicalOrthogonal.formD 3 (ZMod 2) (f ((ρ.comp J.subtype) h v)) = _
      rw [hh]
      exact Representation.BinaryLinearRecognition.orthogonalEightAction_preserves_form _ _
    let : IsIrreducible (ρ.comp J.subtype) := s.hypothesis.irreducible
    have hz := BinaryQuadraticConstituent.quadratic_eq_zero_of_not_self_dual (ρ.comp J.subtype)
      (by change 1 < finrank (ZMod 2) U; have := s.dimension_gt_two; omega) q hq s.not_selfDual
    have hval := congrArg (fun q : QuadraticForm (ZMod 2) U => q (f.symm (fun _ => 1))) hz
    change ClassicalOrthogonal.formD 3 (ZMod 2) (f (f.symm (fun _ => 1))) = 0 at hval
    rw [f.apply_symm_apply] at hval
    norm_num [ClassicalOrthogonal.formD_apply, Fin.sum_univ_three] at hval
    exact (by decide : (3 : ZMod 2) ≠ 0) hval

private theorem not_binary_linear_five_equiv
    (e : J ≃* PSL(5, ZMod 2)) : False := by
  let E := e.trans Representation.SL5TenDimensional.projectiveEquiv.symm
  let σ := (ρ.comp J.subtype).comp E.symm.toMonoidHom
  have hi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective
      (ρ.comp J.subtype)).mpr s.hypothesis.irreducible
  have hf : Function.Injective σ := s.faithful.comp E.symm.injective
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := _root_.BinaryLinear.AutomorphismTwoRank.psl5_two_rank_le
  have hd : finrank (ZMod 2) U ≤ 14 := by omega
  rcases ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.finrank_eq_five_or_ten
      σ hf hi hd with h5 | h10
  · exact s.not_binary_linear_natural_degree (by decide) e h5
  · change finrank (ZMod 2) U = 10 at h10
    omega

private theorem image_not_binary_linear_four_or_five :
    ¬ (Nonempty (J ≃* PSL(4, ZMod 2)) ∨
      Nonempty (J ≃* PSL(5, ZMod 2))) := by
  intro h
  rcases h with h | h <;> obtain ⟨e⟩ := h
  · exact s.not_binary_linear_four_equiv (e)
  · exact s.not_binary_linear_five_equiv (e)

open Sporadic.Mathieu

private theorem not_m12_equiv (e : J ≃* M12) : False := by
  have hr : primeRank 2 (MulAut M12) ≤ 7 := by
    apply primeRank_le_of_prime_pow_not_dvd
    rw [← Nat.card_congr M12ExceptionalExtension.automorphismEquiv.toEquiv,
      M12ExceptionalExtension.carrier_order]
    decide
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hl := ChapterG.Section07.MathieuRecognition.ten_le_finrank_of_m12
    (ρ.comp J.subtype) s.faithful e
  change 10 ≤ finrank (ZMod 2) U at hl
  omega

private theorem not_m22_equiv (e : J ≃* M22) : False := by
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m22_automorphism_twoRank_le_five
  have hl := ChapterG.Section07.MathieuRecognition.ten_le_finrank_of_m22
    (ρ.comp J.subtype) s.faithful e
  change 10 ≤ finrank (ZMod 2) U at hl
  omega

private theorem not_m22_central_quotient
    (e : (J) ⧸ center (J) ≃* M22) : False := by
  have hu := s.quotient_rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m22_automorphism_twoRank_le_five
  have hd : 11 ∣ Nat.card (J) := by
    have hq := (center (J)).card_quotient_dvd_card
    rw [Nat.card_congr e.toEquiv, m22_order] at hq
    exact (by norm_num : 11 ∣ 443520).trans hq
  have hl := BinaryPrimeDegree.orderOf_le_finrank (ρ.comp J.subtype) s.faithful
    (by decide : Nat.Prime 11) (by decide) hd
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hl
  change 10 ≤ finrank (ZMod 2) U at hl
  omega

private theorem not_m23_equiv (e : J ≃* M23) : False := by
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m23_automorphism_twoRank_le_four
  have hl := ChapterG.Section07.MathieuRecognition.eleven_le_finrank_of_m23
    (ρ.comp J.subtype) s.faithful e
  change 11 ≤ finrank (ZMod 2) U at hl
  omega

private theorem not_m24_equiv (e : J ≃* M24) : False := by
  let : Group.IsPerfect (J) := s.hypothesis.component.2.toIsPerfect
  let : Group.IsPerfect M24 := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup M24 := m24_isSimpleGroup
  have hz : center M24 = ⊥ := by
    rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative M24 (center_eq_top_iff.mp h)).elim
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m24_automorphism_rank_le_six hz
  have hl := ChapterG.Section07.MathieuRecognition.eleven_le_finrank_of_m24
    (ρ.comp J.subtype) s.faithful e
  change 11 ≤ finrank (ZMod 2) U at hl
  omega

private theorem image_not_mathieu :
    ¬ (Nonempty (J ≃* M12) ∨
      Nonempty (J ≃* M22) ∨
      Nonempty (J ≃* M23) ∨
      Nonempty (J ≃* M24)) := by
  intro h
  rcases h with h | h | h | h <;> obtain ⟨e⟩ := h
  · exact s.not_m12_equiv (e)
  · exact s.not_m22_equiv (e)
  · exact s.not_m23_equiv (e)
  · exact s.not_m24_equiv (e)

private theorem not_triple_alternating_six_central_quotient
    (e : (J) ⧸ center (J) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (J)) = 3) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (J) := {
    toIsPerfect := s.hypothesis.component.2.toIsPerfect
    simple := e.isSimpleGroup }
  let : IsIrreducible (ρ.comp J.subtype) := s.hypothesis.irreducible
  have hr := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.cover_automorphism_two_rank e
  have hd := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.six_dvd_dimension
    e hz (ρ.comp J.subtype) s.faithful
  change 6 ∣ finrank (ZMod 2) U at hd
  have hu := s.rank_bound
  have hp := s.dimension_gt_two
  omega

private theorem image_not_odd_signed_three {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : OddCharacteristic.IsLinearUnitaryThree (J) p) : False := by
  let H := J
  let : IsQuasisimple H := s.hypothesis.component.2
  let : IsIrreducible (ρ.comp H.subtype) := s.hypothesis.irreducible
  have hd := s.rank_bound
  obtain ⟨⟨e⟩,_⟩ := OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (ρ.comp H.subtype) (s.hypothesis.faithful.comp H.subtype_injective)
    hp ho hm (by dsimp [H]; omega)
  exact s.image_not_g2_zmod_two e

private theorem image_not_suzuki {k : ℕ} (hk : 1 ≤ k)
    (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup k) : False := by
  let H := J
  let σ := (ρ.comp H.subtype).comp e.symm.toMonoidHom
  have hf : Function.Injective σ :=
    s.hypothesis.faithful.comp (H.subtype_injective.comp e.symm.injective)
  have hl := Representation.Suzuki.finrank_ge hk σ hf
  have hu := s.rank_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := BenderSuzuki.MatrixGroups.suzuki_automorphism_two_rank k hk
  omega

private theorem image_not_triple_alternating_seven
    (e : J ⧸ center (J) ≃*
      alternatingGroup (Fin 7))
    (hz : Nat.card (center (J)) = 3) : False := by
  let H := J
  let : IsQuasisimple H := s.hypothesis.component.2
  let : IsIrreducible (ρ.comp H.subtype) := s.hypothesis.irreducible
  have hr := AlternatingSevenCover.cover_automorphism_two_rank e
  have hl := AlternatingSevenCover.six_dvd_dimension e hz
    (ρ.comp H.subtype) (s.hypothesis.faithful.comp H.subtype_injective)
  have hu := s.rank_bound
  have hp := s.dimension_gt_two
  omega

private theorem image_not_remaining_sporadic [IsSimpleGroup (J)] :
    ¬ (Nonempty (J ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (J ≃* Held.He) ∨
      Nonempty (J ≃* Janko4.Model) ∨
      Nonempty (J ≃* Rudvalis.Model) ∨
      Nonempty (J ≃* Sporadic.LeechRelated.J2.Carrier)) := by
  intro hm
  have h := s.hypothesis
  rcases hm with hm | hm | hm | hm | hm
  · exact h.not_higman_sims hm.some
  · exact h.not_held hm.some
  · exact h.not_janko_four hm.some
  · exact h.not_rudvalis hm.some
  · apply h.not_janko_two_of_sharp_degree ?_ hm.some
    have := s.dimension_gt_two
    omega

omit s in
private def centerQuotientCongr {D E : Type*} [Group D] [Group E] (e : D ≃* E) :
    D ⧸ center D ≃* E ⧸ center E :=
  QuotientGroup.congr _ _ e (by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hz
      refine ⟨((centerCongr e).symm ⟨z,hz⟩ : D),
        ((centerCongr e).symm ⟨z,hz⟩).property, ?_⟩
      exact congrArg Subtype.val ((centerCongr e).apply_symm_apply ⟨z,hz⟩))

omit s in
private def BinaryThree (J : Type*) [Group J] : Prop :=
  ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (J ⧸ center J) 3 (2 ^ n)

open Chapter1.Section02 ClassificationModels
open ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

private def simple_center_quotient [IsSimpleGroup J] : J ⧸ center J ≃* J := by
  let : IsQuasisimple J := s.hypothesis.component.2
  have hz : center J = ⊥ := by
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp ht)).elim
  exact (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot

private theorem simple_models [IsSimpleGroup J] (hm : LocalModels.TheoremCModel J) :
    Nonempty (J ≃* alternatingGroup (Fin 7)) ∨ BinaryThree J := by
  have h := s.hypothesis
  have q := s.simple_center_quotient
  cases hm with
  | alternating n hn hm =>
    obtain ⟨e⟩ := hm
    obtain ⟨hnl,hnu⟩ := hn
    interval_cases n
    · exact (s.image_not_binary_rank_one (by decide : 2 ≤ 2)
        (by simpa only [Nat.card_eq_fintype_card] using GaloisField.card 2 2 (by decide))
        ((e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm).trans
          (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm)).elim
    · exact (s.image_not_alternating_six e).elim
    · exact Or.inl ⟨e⟩
    · exact (s.image_not_binary_linear_four_or_five
        (Or.inl ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩)).elim
  | linear_odd p e hp ho he _ hm =>
    let : IsQuasisimple J := h.component.2
    have hd := s.rank_bound
    rcases OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
      (ρ.comp J.subtype) s.faithful hp ho (by rcases he with rfl | rfl <;> omega)
      hm (by omega) with hb | ht | hs
    · obtain ⟨K,_,_,hK,⟨f⟩⟩ := hb
      let : Fintype K := Fintype.ofFinite K
      let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
        (by simpa only [← Nat.card_eq_fintype_card, Nat.reducePow] using hK)
      exact (s.image_not_binary_rank_one (by decide : 2 ≤ 2)
        (by simpa only [Nat.reducePow] using hK) (f.trans (Theory.PSL2.sl2QuotientEquiv K).symm)).elim
    · obtain ⟨K,_,_,hK,⟨f⟩⟩ := ht
      exact Or.inr ⟨1,by decide,K,inferInstance,inferInstance,by simpa using hK,⟨q.trans f⟩⟩
    · exact (s.image_not_binary_symplectic_four (by simp) (Classical.choice hs)).elim
  | three_odd p hp ho unitary hm =>
    apply False.elim
    apply s.image_not_odd_signed_three hp ho
    cases unitary
    · exact Or.inl hm
    · exact Or.inr (Or.inr (Or.inl hm))
  | rank_one hm =>
    apply False.elim
    cases hm with
    | linear n hn hm =>
      obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
      let : Fintype K := Fintype.ofFinite K
      let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by simpa only [← Nat.card_eq_fintype_card] using hK)
      exact s.image_not_binary_rank_one hn hK (e.trans (Theory.PSL2.sl2QuotientEquiv K).symm)
    | unitary n hn hm =>
      obtain ⟨K,_,_,J,hK,hconj,he⟩ := hm
      exact not_unitary_three_positive_exponent h J (by omega) hK hconj (Or.inr he)
    | suzuki k hk he => exact s.image_not_suzuki hk he.some
  | rank_two hm =>
    cases hm with
    | linear n hn hm =>
      obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
      exact Or.inr ⟨n,hn,K,inferInstance,inferInstance,hK,⟨q.trans e⟩⟩
    | symplectic n hn hm =>
      obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
      let : CharP K 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hK
      exact (s.image_not_symplectic_four (by omega) hK
        ((e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm).trans
          (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hK hn).symm)).elim
    | g2 n hn hm =>
      obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
      let : Fintype K := Fintype.ofFinite K
      let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by simpa only [← Nat.card_eq_fintype_card] using hK)
      let : Group.IsPerfect (Atlas.G2.Model K) := Atlas.G2.isPerfect (by
        rw [hK]; exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) (by omega))
      let er : commutator (Atlas.G2.Model K) ≃* Atlas.G2.Model K :=
        (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
      exact (s.image_not_g2 (by omega) hK (e.trans er.symm)).elim
    | triality n hn hm => exact (not_triality_positive_exponent h hn hm).elim
    | ree k hk hm =>
      obtain ⟨d,⟨e⟩⟩ := hm
      exact (not_ree_of_local_block h hk d e).elim
    | symplectic_derived he =>
      exact (s.image_not_alternating_six
        (he.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).elim
    | g2_derived he => exact (s.image_not_g2_zmod_two he.some).elim
    | tits he => exact (not_tits_of_source_component h he.some).elim
  | binary_linear n hn hm =>
    obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
    let : Fintype K := Fintype.ofFinite K
    let f : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hK)).symm
    have e' := e.trans (Atlas.fieldEquivPSL n f)
    apply False.elim
    apply s.image_not_binary_linear_four_or_five
    rcases hn with rfl | rfl
    · exact Or.inl ⟨e'⟩
    · exact Or.inr ⟨e'⟩
  | sporadic name hne he =>
    apply False.elim
    cases name with
    | m11 => exact h.not_m11_central_quotient (q.trans he.some)
    | m12 => exact s.image_not_mathieu (Or.inl he)
    | m22 => exact s.image_not_mathieu (Or.inr (Or.inl he))
    | m23 => exact s.image_not_mathieu (Or.inr (Or.inr (Or.inl he)))
    | m24 => exact s.image_not_mathieu (Or.inr (Or.inr (Or.inr he)))
    | j2 => exact s.image_not_remaining_sporadic (Or.inr (Or.inr (Or.inr (Or.inr he))))
    | j3 => exact hne rfl
    | j4 => exact s.image_not_remaining_sporadic (Or.inr (Or.inr (Or.inl he)))
    | hs => exact s.image_not_remaining_sporadic (Or.inl he)
    | he => exact s.image_not_remaining_sporadic (Or.inr (Or.inl he))
    | ru => exact s.image_not_remaining_sporadic (Or.inr (Or.inr (Or.inr (Or.inl he))))
  | janko_one he => exact (h.not_j1_central_quotient (q.trans he.some)).elim

private theorem three_cover_models (hm : LocalModels.ThreeCoverModel J) : BinaryThree J := by
  have h := s.hypothesis
  cases hm with
  | classical unitary q hq hm =>
    cases unitary
    · change LocalModels.IsSL _ 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
        exact ⟨n,hn,K,inferInstance,inferInstance,hK,⟨centerQuotientCongr e⟩⟩
      · exact (s.image_not_odd_signed_three hp ho (Or.inr (Or.inl hm))).elim
    · change LocalModels.IsSU _ 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · obtain ⟨K,_,_,J,hK,hconj,he⟩ := hm
        exact (not_unitary_three_positive_exponent h J hn hK hconj (Or.inl he)).elim
      · exact (s.image_not_odd_signed_three hp ho (Or.inr (Or.inr (Or.inr hm)))).elim
  | alternating_six hm =>
    exact (s.not_triple_alternating_six_central_quotient hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | alternating_seven hm =>
    exact (s.image_not_triple_alternating_seven hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | mathieu hm => exact (s.not_m22_central_quotient hm.2.2.some).elim

private theorem carrier_models :
    Nonempty (J ≃* alternatingGroup (Fin 7)) ∨ BinaryThree J := by
  rcases s.hypothesis.single_component_models with ⟨hs,hm⟩ | ⟨_,hm⟩
  · let := hs
    exact s.simple_models hm
  · exact Or.inr (s.three_cover_models hm)
end SharpAction
variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
  {v : U} {W : Submodule (ZMod 2) U} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

private theorem actor_conjugation_faithful
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I)
    (hc : ExchangedGeometry.CompletedData ρ B C X I hI) :
    letI := componentOrbit_top_normal C
    Function.Injective (MulAut.conjNormal.comp X.subtype : X →* MulAut (componentOrbit C ⊤)) := by
  let H := componentOrbit C ⊤
  let := componentOrbit_top_normal C
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
  let f : X →* MulAut H := MulAut.conjNormal.comp X.subtype
  apply (injective_iff_map_eq_one f).mpr
  intro z hz
  have hzi : (z : D)⁻¹ = z := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (z : D) z.property)
  have hzI : (z : D) ∈ subspaceStabilizer ρ I := by
    by_contra hn
    have hm : I.map (ρ (z : D)⁻¹) ≠ I := by
      rw [hzi]
      exact fun he => hn ((subspace_map_eq_iff ρ I _).mp he)
    have ho := hI.conjugation_not_inner ρ hfix z hm
    apply ho
    change f z ∈ MulAut.innerSubgroup H
    rw [hz]
    exact (MulAut.innerSubgroup H).one_mem
  have hzc : (z : D) ∈ centralizer (H : Set D) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact hz
  have he := h.spanning_constituent_stabilizer_centralizer_eq_bot hI.isIrrPlus hc.2.1
  apply Subtype.ext
  apply mem_bot.mp
  rw [← he]
  exact ⟨⟨hzI,z.property⟩,hzc⟩

/-- The original whole actor bounds the A7 constituent by four, not five.
The faithful action and the element of order five give the reverse bound. -/
public theorem alternating_seven_degree
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I)
    (hc : ExchangedGeometry.CompletedData ρ B C X I hI)
    (hf : Function.Injective (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation)
    (hbalance : 2 * (Group.rank X + 1) = finrank (ZMod 2) U)
    (e : componentOrbit C ⊤ ≃* alternatingGroup (Fin 7)) :
    finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) U = 8 := by
  let H := componentOrbit C ⊤
  let := componentOrbit_top_normal C
  let f : X →* MulAut (alternatingGroup (Fin 7)) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal.comp X.subtype)
  have hinj : Function.Injective f := (MulAut.congr e).injective.comp
    (actor_conjugation_faithful h hn hC hI hc)
  let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_injective
    (MonoidHom.ofInjective hinj).symm.toMonoidHom (MonoidHom.ofInjective hinj).symm.injective
  have hr := f.range.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 f.range)
  rw [← Group.rank_congr (MonoidHom.ofInjective hinj)] at hr
  have hu := hr.trans ChapterG.Section07.AlternatingSevenCover.alternating_seven_automorphism_two_rank
  obtain ⟨_,_,_,hd⟩ := hc.2.2.1
  have hp : 5 ∣ Nat.card H := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hl := BinaryPrimeDegree.orderOf_le_finrank
    (invariantSubspace ρ H I hI.invariant).toRepresentation hf
    (by decide : Nat.Prime 5) (by decide : 5 ≠ 2) hp
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hl
  change 4 ≤ finrank (ZMod 2) I at hl
  exact ⟨by omega,by omega⟩

/-- The literal normal component in the isotropic branch is A7. The genuine
G.9 input and its model catalogue are consumed; no model is assumed. -/
public theorem component_alternating_seven
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I)
    (hc : ExchangedGeometry.CompletedData ρ B C X I hI)
    (hiso : ∀ u ∈ I, ∀ w ∈ I, B u w = 0)
    (hi : ExchangedIsotropic.IsotropicData ρ C X I hI)
    (S : Sylow 2 D) (hXS : X ≤ (S : Subgroup D))
    (hSX : (S : Subgroup D) ≤ normalizer (X : Set D)) :
    Nonempty (C ≃* alternatingGroup (Fin 7)) := by
  let H := componentOrbit C ⊤
  let image := ExchangedAction.image ρ H X I hI.invariant
  let σ := ExchangedAction.imageAction ρ H X I hI.invariant
  have hf : Function.Injective (invariantSubspace ρ H I hI.invariant).toRepresentation := by
    rcases hc.2.2.2.2.2.2 with hnd | ⟨_,hf,_,_⟩
    · exfalso
      apply hI.isIrrPlus.ne_bot ρ
      apply le_bot_iff.mp
      intro u hu
      have hz : (⟨u,hu⟩ : I) = 0 := hnd.1 ⟨u,hu⟩ (fun w => hiso u hu w w.property)
      exact congrArg Subtype.val hz
    · exact fun a b hab => hf (Units.ext hab)
  let e := ExchangedAction.orbitEquiv ρ H X I hI.invariant hf
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let s : SharpAction σ (image (ExchangedAction.actor ρ X I)) (image H) := {
    hypothesis := hi.2.2.1
    dimension_gt_two := hI.isIrrPlus.finrank_gt_two ρ H
    not_selfDual := hi.2.2.2.1
    proper := hi.2.2.2.2.1 }
  rcases s.carrier_models with ha | ⟨n,hnpos,K,_,_,hK,⟨q⟩⟩
  · exact ⟨((MulEquiv.subgroupCongr hi.1.symm).trans e).trans ha.some⟩
  · let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [← Nat.card_eq_fintype_card] using hK)
    exact (ExchangedIsotropic.not_binary_linear_three_central_quotient h hn hC hI hc S
      hXS hSX hnpos hK ((SharpAction.centerQuotientCongr e).trans q)).elim

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropicModels

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor CoreGeometry
open LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- Apply the full carrier sieve to the original rank-three flag. The
nondegenerate alternative and all original action markings are retained. -/
public theorem source_exchanged_recognized_component_input (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I) :
    ExchangedGeometry.CompletedData F.terminalRepresentation B C (F.terminalDot (F.X g)) I hI ∧
    ((B.restrict I).Nondegenerate ∨
      ((∀ a ∈ I, ∀ b ∈ I, B a b = 0) ∧
        ExchangedIsotropic.IsotropicData F.terminalRepresentation C
          (F.terminalDot (F.X g)) I hI ∧
        Nonempty (C ≃* alternatingGroup (Fin 7)) ∧
        finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) (Additive F.Uhat) = 8)) := by
  obtain ⟨hc,hd⟩ := source_exchanged_component_input d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  refine ⟨hc,?_⟩
  rcases hd with hnd | ⟨hiso,hi⟩
  · exact Or.inl hnd
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hnonsolv := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  obtain ⟨e⟩ := ExchangedIsotropicModels.component_alternating_seven hyp hnonsolv hC
    hI hc hiso hi P hXP ((normal_subgroupOf_iff_le_normalizer hXP).mp hN)
  have hf : Function.Injective (invariantSubspace F.terminalRepresentation
      (componentOrbit C ⊤) I hI.invariant).toRepresentation := by
    rcases hc.2.2.2.2.2.2 with hnd | ⟨_,hf,_,_⟩
    · exfalso
      apply hI.isIrrPlus.ne_bot F.terminalRepresentation
      apply le_bot_iff.mp
      intro u hu
      exact congrArg Subtype.val (hnd.1 ⟨u,hu⟩ (fun w => hiso u hu w w.property))
    · exact fun a b hab => hf (Units.ext hab)
  obtain ⟨_,hE,hX,_⟩ := source_terminal_ranks_of_no_lowRank d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hline hn
  have hb : 2 * (Group.rank (F.terminalDot (F.X g)) + 1) =
      finrank (ZMod 2) (Additive F.Uhat) := by omega
  have hd := ExchangedIsotropicModels.alternating_seven_degree hyp hnonsolv hC hI hc hf hb
    ((MulEquiv.subgroupCongr hi.1).trans e)
  exact Or.inr ⟨hiso,hi,⟨e⟩,hd⟩

namespace FixedLineReduction
/-- The original remainder now has an actual A7 component
in its isotropic branch. The nondegenerate branch and every original
marking, fixed-point clause and mixed-size premise are retained. -/
public theorem source_large_recognized_isotropic_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
      ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
        ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
        ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
        ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
            (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
          v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
          ExchangedGeometry.CompletedData F.terminalRepresentation B C
            (F.terminalDot (F.X g)) I hI ∧
          ((B.restrict I).Nondegenerate ∨
            ((∀ a ∈ I, ∀ b ∈ I, B a b = 0) ∧
              ExchangedIsotropic.IsotropicData F.terminalRepresentation C
                (F.terminalDot (F.X g)) I hI ∧
              Nonempty (C ≃* alternatingGroup (Fin 7)) ∧
        finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) (Additive F.Uhat) = 8)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo⟩ :=
    source_large_exchanged_remainder_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  exact ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,
    source_exchanged_recognized_component_input d earlier hq chosen structural alternatives F hne hZ hlarge
      g hgP hgH hyp hline hn hC hm hI hv⟩
end FixedLineReduction
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
