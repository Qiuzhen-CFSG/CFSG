module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveBounds
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Models
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank
public import Theory.Representation.BinaryQuadraticConstituent

/-!
# The triple-cover and two-component rows in the exchanged sieve

The triple A₆ cover has degree divisible by six and automorphism rank at
most three, contradicting the sharp exchanged bound. The corrected tensor
row is an identification of the H-action: its nine-dimensional module is
too large for the automorphism rank of the actual PSL₃(2) square. No action
of the whole constituent quotient is identified with the tensor model.

The orthogonal row preserves its defining field-valued quadratic form.
A binary linear functional nonzero at one gives a nonzero invariant binary
quadratic form on the same H-module, contradicting non-self-duality. Thus
this exclusion also preserves the exact group action, including field twists.

Source: Aschbacher--Smith G.9.3(5),(14),(15), G.11.6, printed pp.354,366.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups TensorProduct
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

include s


/-- The triple cover of A₆ has positive degree divisible by six, whereas
its automorphism rank and the exchanged bound force degree at most five. -/
theorem not_triple_alternating_six_central_quotient
    (e : (componentOrbit L ⊤) ⧸ center (componentOrbit L ⊤) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (componentOrbit L ⊤)) = 3) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (componentOrbit L ⊤) := {
    toIsPerfect := s.component.orbit_isPerfect ⊤
    simple := e.isSimpleGroup }
  let : IsIrreducible s.orbitAction := s.irreducible
  have hr := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.cover_automorphism_two_rank e
  have hd := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.six_dvd_dimension
    e hz s.orbitAction s.orbit_faithful
  change 6 ∣ finrank (ZMod 2) I at hd
  have hu := s.orbit_degree_le_automorphism_rank_add_two
  have hp := s.dimension_gt_two
  omega

/-- The triple-cover row is excluded after the literal action quotient too. -/
theorem image_not_triple_alternating_six_central_quotient
    (e : (s.image (componentOrbit L ⊤)) ⧸ center (s.image (componentOrbit L ⊤)) ≃*
      alternatingGroup (Fin 6))
    (hz : Nat.card (center (s.image (componentOrbit L ⊤))) = 3) : False := by
  let : Group.IsPerfect (componentOrbit L ⊤) := s.component.orbit_isPerfect ⊤
  let f : PerfectCentralCovering.Cover (componentOrbit L ⊤) (s.image (componentOrbit L ⊤)) := {
    toMonoidHom := s.orbitEquiv.toMonoidHom
    surjective := s.orbitEquiv.surjective
    isPerfect := inferInstance
    ker_le_center := by rw [s.orbitEquiv.toMonoidHom.ker_eq_bot_iff.mpr s.orbitEquiv.injective]; exact bot_le }
  exact s.not_triple_alternating_six_central_quotient (f.quotientCenterEquiv.trans e)
    ((Nat.card_congr (centerCongr s.orbitEquiv).toEquiv).trans hz)

/-- Exclude the corrected tensor row on H. No whole-quotient tensor model,
actor replacement or supplied rank-four conclusion is used. -/
theorem image_not_three_tensor
    (hq : ChapterG.Section09.Quasiequivalent
      (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
      ChapterG.Section09.TwoComponents.threeTensor) : False := by
  obtain ⟨e,f,_⟩ := hq
  have hd := f.finrank_eq.trans ChapterG.Section09.TwoComponents.threeTensor_degree
  have hr : primeRank 2 (MulAut PSL(3,ZMod 2)) = 2 :=
    Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two (ZMod 2) (by simp)
  let : Group.IsPerfect SL(3,ZMod 2) := Atlas.sl_perfect 3 (by decide)
  have hz : center PSL(3,ZMod 2) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot SL(3,ZMod 2)
  have hp : 0 < primeRank 2 (MulAut PSL(3,ZMod 2)) := by omega
  have hr2 := AutomorphismSquare.rank_bound hz hp
  rw [hr] at hr2
  have hu := s.image_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  change finrank (ZMod 2) I ≤ primeRank 2 (MulAut (PSL(3,ZMod 2) × PSL(3,ZMod 2))) + 2 at hu
  change finrank (ZMod 2) I = 9 at hd
  change primeRank 2 (MulAut (PSL(3,ZMod 2) × PSL(3,ZMod 2))) ≤ 2 * 2 at hr2
  omega

/-- The orthogonal two-factor row preserves a nonzero binary quadratic form
on the same H-module, contradicting the faithful exchanged non-self-duality. -/
theorem image_not_four_orthogonal (n : ℕ)
    (hq : ChapterG.Section09.Quasiequivalent
      (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
      (ChapterG.Section09.TwoComponents.fourOrthogonal n)) : False := by
  obtain ⟨e,f,hf⟩ := hq
  obtain ⟨ell,hell⟩ := Module.Projective.exists_dual_eq_one (ZMod 2)
    (show (1 : GaloisField 2 n) ≠ 0 from one_ne_zero)
  let Q := ell.compQuadraticMap' (ClassicalOrthogonal.formD 2 (GaloisField 2 n))
  let q := Q.comp f.toLinearMap
  have hinv : ∀ a v, q ((s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype) a v) = q v := by
    intro a v
    change ell (ClassicalOrthogonal.formD 2 (GaloisField 2 n) (f (s.imageAction a v))) = _
    have hfv := hf a v
    change f (s.imageAction a v) =
      ChapterG.Section09.TwoComponents.fourOrthogonal n (e a) (f v) at hfv
    rw [hfv]
    exact congrArg ell (ClassicalOrthogonal.subgroupNatural_preserves
      (ClassicalOrthogonal.OmegaPlus 2 (GaloisField 2 n)) (e a) (f v))
  let : IsIrreducible (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype) :=
    s.image_irreducible
  have hz := BinaryQuadraticConstituent.quadratic_eq_zero_of_not_self_dual
    (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
    (by have := s.dimension_gt_two; omega) q hinv s.image_not_selfDual
  let w : ClassicalOrthogonal.VectorD 2 (GaloisField 2 n) := Sum.elim ![1,0] ![1,0]
  have hval := congrArg (fun q : QuadraticForm (ZMod 2) I => q (f.symm w)) hz
  change ell (ClassicalOrthogonal.formD 2 (GaloisField 2 n) (f (f.symm w))) = 0 at hval
  rw [f.apply_symm_apply] at hval
  simp [w, ClassicalOrthogonal.formD_apply, Fin.sum_univ_two, hell] at hval

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
