module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveSelfDual
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.Component
public import Theory.Representation.SL2OrthogonalCover.Universal
public import Theory.Representation.BinaryQuadraticConstituent

/-!
# All binary rank-one models in the faithful exchanged branch

The sharp bound gives dim(I) ≤ n+2. The complete small SL₂ catalogue then
leaves the natural action, the Hermitian action, or the degree-eight triple
at n=3. The first is self-dual; the Hermitian determinant supplies a nonzero
invariant binary quadratic form; and degree eight contradicts the sharp
bound. The image-group exclusion assumes no module identification.

Source: Aschbacher--Smith G.9.3(6),(7),(16), G.11.6, pp.354,366.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace ExchangedFaithfulSource
attribute [local instance] ZMod.algebra
local instance hermitianBinaryModule (n : ℕ) [NeZero n] :
    Module (ZMod 2) (OrthogonalFourMinus.FiniteModel.Space n) :=
  Module.compHom _ (algebraMap (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField n))
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)
  {K : Type*} [Field K] [Finite K] [CharP K 2]

include s

/-- The actual natural SL₂ action is self-dual on the same H-image. -/
theorem image_not_rank_one_natural
    (hq : ChapterG.Section09.Quasiequivalent
      (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
      (SL2.BinarySmall.natural (K := K))) : False := by
  apply s.image_not_selfDual
  apply ExchangedAction.selfDual_of_quasiequivalent hq
  refine .mk (SL2OrthogonalCover.binarySelfDual (F := K)) ?_
  intro a
  apply LinearMap.ext
  intro w
  exact SL2OrthogonalCover.binarySelfDual_equivariant a w

set_option backward.isDefEq.respectTransparency false in
theorem image_not_rank_one_hermitian (n : ℕ) [NeZero n]
    (hq : ChapterG.Section09.Quasiequivalent
      (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
      (SL2.BinarySmall.hermitian n)) : False := by
  obtain ⟨e,f,hf⟩ := hq
  obtain ⟨ell,hell⟩ := Module.Projective.exists_dual_eq_one (ZMod 2)
    (show (1 : OrthogonalFourMinus.FiniteModel.fixedField n) ≠ 0 from one_ne_zero)
  have hzform := (OrthogonalFourMinus.FiniteModel.form n).map_zero
  change OrthogonalFourMinus.FiniteModel.determinant n 0 = 0 at hzform
  let q : QuadraticForm (ZMod 2) I := QuadraticMap.ofPolar
    (fun w => ell (OrthogonalFourMinus.FiniteModel.form n (f w)))
    (by intro a w; fin_cases a <;> simp [hzform])
    (by
      intro x y z
      simpa only [QuadraticMap.polar, map_add, map_sub] using
        congrArg ell ((OrthogonalFourMinus.FiniteModel.form n).polar_add_left (f x) (f y) (f z)))
    (by intro a x y; fin_cases a <;> simp [QuadraticMap.polar, hzform])
  have hinv : ∀ a w, q ((s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype) a w) = q w := by
    intro a w
    change ell (OrthogonalFourMinus.FiniteModel.form n (f (s.imageAction a w))) = _
    have hfw := hf a w
    change f (s.imageAction a w) = SL2.BinarySmall.hermitian n (e a) (f w) at hfw
    rw [hfw]
    exact congrArg ell (OrthogonalFourMinus.FiniteModel.form_preserved n (e a) (f w))
  let : IsIrreducible (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype) := s.image_irreducible
  have hz := BinaryQuadraticConstituent.quadratic_eq_zero_of_not_self_dual
    (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
    (by have := s.dimension_gt_two; omega) q hinv s.image_not_selfDual
  let w := (OrthogonalFourMinus.FiniteModel.coordinates n).symm ((1,1),0)
  have hval := congrArg (fun q : QuadraticForm (ZMod 2) I => q (f.symm w)) hz
  change ell (OrthogonalFourMinus.FiniteModel.form n (f (f.symm w))) = 0 at hval
  rw [f.apply_symm_apply] at hval
  have hw : OrthogonalFourMinus.FiniteModel.form n w = 1 := by
    rw [OrthogonalFourMinus.FiniteModel.form_coordinates]
    simp only [one_mul, sub_eq_self]
    apply Subtype.ext
    simp [OrthogonalFourMinus.FiniteModel.norm]
  rw [hw,hell] at hval
  exact one_ne_zero hval

/-- The sharp degree bound eliminates all actual binary rank-one H models;
no natural-module identification is assumed. -/
theorem image_not_binary_rank_one {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : s.image (componentOrbit L ⊤) ≃* SL(2,K)) : False := by
  let H := s.image (componentOrbit L ⊤)
  let σ := (s.imageAction.comp H.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (s.imageAction.comp H.subtype)).mpr s.image_irreducible
  have hf : Function.Injective σ :=
    s.image_setup.faithful.comp (H.subtype_injective.comp e.symm.injective)
  have hu := s.image_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hK
  have hd : finrank (ZMod 2) I ≤ n + 2 := by omega
  rcases ChapterG.Section09.DefiningCharacteristic.binary_small_faithful_classification
      σ hf n hn hK (by omega) with hnat | hherm | htriple
  · obtain ⟨a⟩ := hnat.2.2
    apply s.image_not_rank_one_natural (K := K)
    refine ⟨e,a.toLinearEquiv,?_⟩
    intro x w
    have hh := LinearMap.congr_fun (a.toIntertwiningMap.isIntertwining' (e x)) w
    change a.toLinearEquiv (s.imageAction (H.subtype (e.symm (e x))) w) =
      SL2.BinarySmall.natural (e x) (a.toLinearEquiv w) at hh
    change a.toLinearEquiv (s.imageAction (H.subtype x) w) =
      SL2.BinarySmall.natural (e x) (a.toLinearEquiv w)
    simpa only [MulEquiv.symm_apply_apply] using hh
  · obtain ⟨_,_,t,ht⟩ := hherm
    obtain ⟨k,⟨a⟩⟩ := ht
    let : NeZero (finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] (Representation.asModule σ))) := ⟨t.ne'⟩
    apply s.image_not_rank_one_hermitian (finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] (Representation.asModule σ)))
    refine ⟨e.trans (Atlas.fieldEquivSL 2 k),a.toLinearEquiv,?_⟩
    intro x w
    have hh := LinearMap.congr_fun (a.toIntertwiningMap.isIntertwining' (e x)) w
    change a.toLinearEquiv (s.imageAction (H.subtype (e.symm (e x))) w) =
      SL2.BinarySmall.hermitian (finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] (Representation.asModule σ))) ((Matrix.SpecialLinearGroup.map k.toRingHom) (e x))
        (a.toLinearEquiv w) at hh
    change a.toLinearEquiv (s.imageAction (H.subtype x) w) =
      SL2.BinarySmall.hermitian (finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] (Representation.asModule σ))) ((Matrix.SpecialLinearGroup.map k.toRingHom) (e x))
        (a.toLinearEquiv w)
    simpa only [MulEquiv.symm_apply_apply] using hh
  · have h3 := htriple.2.1
    have h8 := htriple.2.2.1
    omega


end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
