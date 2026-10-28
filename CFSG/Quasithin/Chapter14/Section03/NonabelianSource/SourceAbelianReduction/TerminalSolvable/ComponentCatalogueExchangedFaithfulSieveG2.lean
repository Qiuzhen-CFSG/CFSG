module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveSelfDual
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.OrbitBounds
public import Theory.SpecificGroups.G2Even.TwoRank.SourceBound
public import Theory.SpecificGroups.G2Even.BinaryDerivedAutomorphismRank
public import Theory.Representation.G2OrthogonalCover.Universal
public import Theory.Representation.NonsplitFour

/-!
# All derived G₂ images in the faithful exchanged branch

For n≥2 the actual Schur tensor-degree formula and the small-block
arithmetic force dimension 6n; the exchanged bound is at most 3n+2.
At n=1, degree at most five contradicts divisibility of the faithful linear
group order by 27. Field transport restricts the genuine octonion group
equivalence to its commutator subgroup. The natural row also has an explicit
same-action self-duality exclusion, with no dimension argument required.

Source: Aschbacher--Smith G.9.3(10), G.11.6, printed pp.354,366.
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

/-- The genuine derived G₂ natural row, including the binary derived group,
has an invariant nondegenerate pairing on exactly the identified H-action. -/
theorem image_not_g2_natural
    (hq : ChapterG.Section09.Quasiequivalent
      (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
      (ChapterG.Section09.DefiningCharacteristic.G2Recognition.derivedNaturalBinary K)) : False := by
  apply s.image_not_selfDual
  apply ExchangedAction.selfDual_of_quasiequivalent hq
  refine .mk (Atlas.G2.Natural.OrthogonalCover.binarySelfDual K) ?_
  intro a
  apply LinearMap.ext
  intro w
  exact Atlas.G2.Natural.OrthogonalCover.binarySelfDual_equivariant K a w

/-- The full nonbinary G₂ tensor-degree theorem contradicts the sharp
exchanged bound, without requiring a natural-module recognition premise. -/
theorem image_not_nonbinary_g2 {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : s.image (componentOrbit L ⊤) ≃* commutator (Atlas.G2.Model K)) : False := by
  have hq : 2 < Nat.card K := by
    rw [hK]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  let : Group.IsPerfect (Atlas.G2.Model K) := Atlas.G2.isPerfect hq
  let E : s.image (componentOrbit L ⊤) ≃* Atlas.G2.Model K :=
    e.trans ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv)
  let H := s.image (componentOrbit L ⊤)
  let σ := (s.imageAction.comp H.subtype).comp E.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective
      (s.imageAction.comp H.subtype)).mpr s.image_irreducible
  have hf : Function.Injective σ :=
    s.image_setup.faithful.comp (H.subtype_injective.comp E.symm.injective)
  have hu := s.image_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr E)] at hu
  have hr := Atlas.G2.EvenTwoRank.source_automorphism_two_rank_le K hn hK
  have hd : finrank (ZMod 2) I ≤ 6 * n + 2 := by omega
  obtain ⟨_,t,l,ht,_,hnt,hdim,hne,hbasic⟩ :=
    ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary.exists_basic_parameters
      σ hn hK hf
  have hp := ChapterG.Section09.DefiningCharacteristic.G2Recognition.small_basic_block_parameters
    l hbasic hne (by omega) ht hnt hdim hd
  omega

/-- At the binary endpoint, order divisibility alone excludes degrees at
most five: 27 divides |G₂(2)′|, but not any of GL₀(2),...,GL₅(2). -/
theorem image_not_g2_zmod_two
    (e : s.image (componentOrbit L ⊤) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hu := s.image_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := Atlas.G2.binary_derived_automorphism_two_rank_le_three
  have hd : finrank (ZMod 2) I ≤ 5 := by omega
  have hc : Nat.card (s.image (componentOrbit L ⊤)) = 6048 := by
    rw [Nat.card_congr e.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.card_H
  have hi : Function.Injective (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype) :=
    s.image_setup.faithful.comp (s.image (componentOrbit L ⊤)).subtype_injective
  have hdiv := Representation.card_dvd_card_GL_of_injective
    (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype) hi
  rw [hc, Matrix.card_GL_field] at hdiv
  simp only [ZMod.card] at hdiv
  have hd27 := (by decide : 27 ∣ 6048).trans hdiv
  interval_cases h : finrank (ZMod 2) I <;> norm_num [Fin.prod_univ_succ] at hd27

omit [CharP K 2] in
/-- The binary field witness is transported through the actual octonion
field equivalence and its restriction to the commutator subgroup. -/
theorem image_not_binary_g2 (hK : Nat.card K = 2)
    (e : s.image (componentOrbit L ⊤) ≃* commutator (Atlas.G2.Model K)) : False := by
  let a := Atlas.G2.fieldEquiv (Atlas.G2.binaryFieldEquiv hK)
  let f : commutator (Atlas.G2.Model K) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
    (a.subgroupMap _).trans (MulEquiv.subgroupCongr (by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr a.surjective, commutator_def]))
  exact s.image_not_g2_zmod_two (e.trans f)

/-- Every positive binary exponent of the genuine derived G₂ family is
excluded on the same faithful H image. -/
theorem image_not_g2 {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2 ^ n)
    (e : s.image (componentOrbit L ⊤) ≃* commutator (Atlas.G2.Model K)) : False := by
  by_cases hn1 : n = 1
  · exact s.image_not_binary_g2 (by simpa [hn1] using hK) e
  · exact s.image_not_nonbinary_g2 (by omega) hK e


end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
