module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSourceAction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Literal source-core transport through the point quotient

The original source core is `Q = [O₂(L),L]`.  Passing to the literal point
quotient has a precise effect: the image of `Q` is the commutator core of the
image of `L`.  This is an equality, not merely a containment, because the
quotient kernel is a 2-group and embedded 2-cores commute with such images.
The same statement applies to a conjugate source core when its conjugate
component itself has been placed in the point centralizer.  Thus a vanishing image is exactly the
statement that the corresponding carrier has trivial commutator core; no
claim that the original core survives the point kernel is made.

The result records the hidden-kernel boundary needed by the finite carrier
packet: it applies to a source subgroup once that subgroup itself has been
placed in the point centralizer.  In particular, containment of a conjugate
core alone does not place the conjugate component, so this lemma does not
silently identify the opposite image with the image of the original
component.  The known order-four opposite image remains a separate statement.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93

/-- A homomorphism with 2-group kernel sends the literal source commutator
core exactly to the commutator core of the image subgroup. -/
theorem binary_three_original_core_image
    {C H : Type*} [Group C] [Group H] [Finite C] [Finite H]
    (A : Subgroup C) (q : C →* H) (hq : IsPGroup 2 q.ker) :
    (LinearThree.commutatorCore A).map q =
      LinearThree.commutatorCore (A.map q) := by
  change (⁅A.pCoreIn 2, A⁆).map q = ⁅(A.map q).pCoreIn 2, A.map q⁆
  rw [map_commutator, map_pCoreIn_of_ker_isPGroup q hq]

/-- A quotient factor whose source kernel is contained in a known 2-group
kernel has the expected point 2-core as its kernel. -/
theorem binary_three_factor_projection
    {A H Q : Type*} [Group A] [Group H] [Group Q]
    [Finite A] [Finite H] [Finite Q]
    (r : A →* H) (f : A →* Q)
    (hr : Function.Surjective r) (hf : Function.Surjective f)
    (hker : r.ker ≤ f.ker) (hfk : IsPGroup 2 f.ker)
    (hq : pCore 2 Q = (⊥ : Subgroup Q)) :
    ∃ φ : H →* Q, Function.Surjective φ ∧ φ.comp r = f ∧
      φ.ker = pCore 2 H := by
  let φ : H →* Q := r.liftOfSurjective hr ⟨f, hker⟩
  have hcomp : φ.comp r = f := by
    apply MonoidHom.ext
    intro x
    exact r.liftOfRightInverse_comp_apply
      (Function.surjInv hr) (Function.rightInverse_surjInv hr) ⟨f, hker⟩ x
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    refine ⟨r x, ?_⟩
    rw [show φ (r x) = f x from congrArg (fun k => k x) hcomp]
    exact hx
  have hker_eq : φ.ker = f.ker.map r := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := hr y
      apply mem_map_of_mem r
      rw [MonoidHom.mem_ker] at hy ⊢
      rw [show φ (r x) = f x from congrArg (fun k => k x) hcomp] at hy
      exact hy
    · rintro y ⟨x, hx, rfl⟩
      rw [MonoidHom.mem_ker]
      rw [show φ (r x) = f x from congrArg (fun k => k x) hcomp]
      exact MonoidHom.mem_ker.mp hx
  have hφp : IsPGroup 2 φ.ker := by
    rw [hker_eq]
    exact hfk.map r
  have hcomap := φ.comap_pCore_of_ker_isPGroup hφ hφp
  rw [hq] at hcomap
  have hkerbot : φ.ker = Subgroup.comap φ (⊥ : Subgroup Q) := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_bot]
  exact ⟨φ, hφ, hcomp, hkerbot.symm.trans hcomap⟩

/-- The original ambient core may first be restricted to a containing point
centralizer.  The equality remains literal after this restriction. -/
theorem binary_three_original_core_image_of_le
    {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H]
    (A Csub : Subgroup G) (hAC : A ≤ Csub)
    (q : Csub →* H) (hq : IsPGroup 2 q.ker) :
    ((LinearThree.commutatorCore A).subgroupOf Csub).map q =
      LinearThree.commutatorCore ((A.subgroupOf Csub).map q) := by
  have hcore : (LinearThree.commutatorCore A).subgroupOf Csub =
      LinearThree.commutatorCore (A.subgroupOf Csub) := by
    change (⁅A.pCoreIn 2, A⁆).subgroupOf Csub =
      ⁅(A.subgroupOf Csub).pCoreIn 2, A.subgroupOf Csub⁆
    apply map_injective Csub.subtype_injective
    rw [map_subgroupOf_eq_of_le
      (((LinearThree.commutatorCore_le A).trans (pCoreIn_le 2 A)).trans hAC)]
    rw [map_commutator, Subgroup.pCoreIn_subgroupOf 2 A Csub hAC,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 A).trans hAC),
      map_subgroupOf_eq_of_le hAC]
  rw [hcore]
  exact binary_three_original_core_image (A.subgroupOf Csub) q hq

/-- If the original source core is killed by the point quotient, then the
resulting carrier has trivial commutator core, and conversely. -/
theorem binary_three_original_core_image_eq_bot_iff
    {C H : Type*} [Group C] [Group H] [Finite C] [Finite H]
    (A : Subgroup C) (q : C →* H) (hq : IsPGroup 2 q.ker) :
    (LinearThree.commutatorCore A).map q = ⊥ ↔
      LinearThree.commutatorCore (A.map q) = ⊥ := by
  rw [binary_three_original_core_image A q hq]


/-- After restriction to a point centralizer, vanishing of the literal source
core image is equivalent to vanishing of the carrier commutator core. -/
theorem binary_three_original_core_image_eq_bot_iff_of_le
    {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H]
    (A Csub : Subgroup G) (hAC : A ≤ Csub)
    (q : Csub →* H) (hq : IsPGroup 2 q.ker) :
    ((LinearThree.commutatorCore A).subgroupOf Csub).map q = ⊥ ↔
      LinearThree.commutatorCore ((A.subgroupOf Csub).map q) = ⊥ := by
  rw [binary_three_original_core_image_of_le A Csub hAC q hq]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
