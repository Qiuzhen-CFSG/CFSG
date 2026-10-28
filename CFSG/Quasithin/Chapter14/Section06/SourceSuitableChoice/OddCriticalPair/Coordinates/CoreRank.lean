module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Parabolic
public import Theory.GroupAction.BinaryWreathPlaneGeometry
public import Theory.GroupTheory.SectionImageLift

/-!
# The core-centralizer rank in the orthogonal branch

The image of C_[U,H](Q_H) in [U,H]/Z is invariant under the full orthogonal
actor. Irreducibility and an actual vector moved by Q_H force that image to
vanish. Thus C_[U,H](Q_H)=Z, and the centralizer quotient of U has order at
least sixteen. This supplies the literal logarithmic rank used by the terminal
consumer; no rank or dual-module identification is assumed.

Source: Aschbacher--Smith 14.6.17--18, printed pp.1035--1036.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
attribute [local instance] orthogonalAction
include h

/-- The core centralizer on the moved group is precisely the central line.
The full orthogonal image makes its image invariant and irreducible, while
noncentrality of the chosen vector excludes the whole moved group. -/
theorem orthogonal_moved_centralizer
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (u : G) (hu : u ∈ ⁅D.UH,D.H⁆)
    (hm : ¬ D.QH ≤ centralizer ({u} : Set G)) :
    ⁅D.UH,D.H⁆ ⊓ centralizer (D.QH : Set G) = D.V₁ := by
  let K := ⁅D.UH,D.H⁆
  let C := K ⊓ centralizer (D.QH : Set G)
  let B := (C.subgroupOf K).map d.coordinates
  have hZC : D.V₁ ≤ C := le_inf d.point_le
    (le_centralizer_iff.mp ((pCoreIn_le 2 D.H).trans h.H_centralizes))
  have hn : D.H ≤ normalizer (C : Set G) :=
    (le_inf (normalizer_commutator_ge_right D.UH D.H)
      ((ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D)).trans (normalizer_le_normalizer_centralizer D.QH))).trans
      inf_normalizer_le_normalizer_inf
  have hinv (a : OrthogonalActor) (v : OrthogonalVector) (hv : v ∈ B) : a • v ∈ B := by
    obtain ⟨x,hx⟩ := d.onto a
    obtain ⟨w,hw,rfl⟩ := hv
    let y := K.normalizerMonoidHom
      ⟨x,normalizer_commutator_ge_right D.UH D.H x.property⟩ w
    have hy : (y : G) ∈ C := (hn x.property w).mp hw
    refine ⟨y,hy,?_⟩
    exact (d.compatible x w).trans (by rw [hx])
  rcases BinaryWreathPointStabilizer.invariant_subgroup_eq_bot_or_top B hinv with hb | hb
  · apply le_antisymm ?_ hZC
    intro x hx
    have hq : d.coordinates ⟨x,hx.1⟩ ∈ B := mem_map_of_mem _ hx
    rw [hb,mem_bot] at hq
    have hh : (⟨x,hx.1⟩ : K) ∈ d.coordinates.ker := hq
    rwa [d.vector_kernel] at hh
  · have hKC : K ≤ C := by
      apply le_of_section_image_le d.coordinates d.vector_kernel le_rfl hZC
      rw [show (C.subgroupOf K).map d.coordinates = ⊤ from hb]
      exact le_top
    exact (hm (le_centralizer_iff.mpr (hKC.trans inf_le_right)
      |>.trans (centralizer_le (Set.singleton_subset_iff.mpr hu)))).elim

/-- The original core-centralizer quotient has rank at least four. -/
theorem orthogonal_module_rank
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (u : G) (hu : u ∈ ⁅D.UH,D.H⁆)
    (hm : ¬ D.QH ≤ centralizer ({u} : Set G)) :
    4 ≤ Nat.log 2 ((centralizer (D.QH : Set G)).relIndex D.UH) := by
  let K := ⁅D.UH,D.H⁆
  have he := orthogonal_moved_centralizer h d u hu hm
  have hsub : (centralizer (D.QH : Set G)).subgroupOf K = D.V₁.subgroupOf K := by
    ext x
    change (x : G) ∈ centralizer (D.QH : Set G) ↔ (x : G) ∈ D.V₁
    exact ⟨fun hx => he ▸ (show (x : G) ∈ K ⊓ centralizer (D.QH : Set G) from
      ⟨x.property,hx⟩),fun hx => (show (x : G) ∈ K ⊓ centralizer (D.QH : Set G) from
        he.symm ▸ hx).2⟩
  have hi : (centralizer (D.QH : Set G)).relIndex K = 16 := by
    change ((centralizer (D.QH : Set G)).subgroupOf K).index = 16
    rw [hsub,←d.vector_kernel,index_ker,MonoidHom.range_eq_top.mpr d.surjective,card_top]
    norm_num [OrthogonalVector,OrthogonalPlaneVector,OrthogonalPlaneIndex,Nat.card_eq_fintype_card]
  let : (centralizer (D.QH : Set G)).IsFiniteRelIndex D.UH :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hle := relIndex_le_of_le_right (H := centralizer (D.QH : Set G))
    (le_normalizer_iff_commutator_le_left.mp d.normalized) (by exact relIndex_ne_zero)
  rw [hi] at hle
  exact Nat.le_log_of_pow_le (by decide) hle

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
