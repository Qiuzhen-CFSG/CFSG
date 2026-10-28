module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Independent conjugation images from disjoint commutators

If two subgroups normalize W and their commutator subgroups with W are
disjoint, their induced automorphism groups on W have trivial intersection.
When the second subgroup normalizes the first, the order of their joined
image is the product of the two image orders, and the centralizer kernel
of the join is the join of the two full centralizer kernels. These identities
do not require faithful ambient actions.

This is the product calculation used for the separated backward seeds in
MS93 (5.11), printed p.923; the original tensor application is in
GenerationTwoSymplecticPairedImages.
-/

public section
open Subgroup
open scoped commutatorElement Pointwise

namespace Subgroup

/-- Disjoint displacement groups make the two conjugation images independent. -/
private theorem conjugation_images_disjoint
    {G : Type*} [Group G] (A B W : Subgroup G)
    (hd : Disjoint ⁅A,W⁆ ⁅B,W⁆) :
    Disjoint ((A.subgroupOf (normalizer (W : Set G))).map W.normalizerMonoidHom)
      ((B.subgroupOf (normalizer (W : Set G))).map W.normalizerMonoidHom) := by
  let S := normalizer (W : Set G)
  let f := W.normalizerMonoidHom
  let A₀ := A.subgroupOf S
  let B₀ := B.subgroupOf S
  have hdis : Disjoint (A₀.map f) (B₀.map f) := by
    apply disjoint_def.mpr
    intro y hyA hyB
    obtain ⟨a,ha,rfl⟩ := hyA
    obtain ⟨b,hb,he⟩ := hyB
    have hc : a.val ∈ centralizer (W : Set G) := by
      intro w hw
      have hew := congrArg (fun e : MulAut W => (e ⟨w,hw⟩).val) he
      change b.val*w*b.val⁻¹ = a.val*w*a.val⁻¹ at hew
      have hcomm : ⁅a.val,w⁆ = ⁅b.val,w⁆ := by
        simp only [commutatorElement_def]
        rw [hew]
      have hz : ⁅a.val,w⁆ = 1 := disjoint_def.mp hd
        (commutator_mem_commutator ha hw) (by rw [hcomm]; exact commutator_mem_commutator hb hw)
      exact (commutatorElement_eq_one_iff_mul_comm.mp hz).symm
    have hk : a ∈ f.ker := by
      rw [normalizerMonoidHom_ker]
      exact hc
    exact hk
  exact hdis

/-- The full centralizer kernel splits over two independent conjugation images. -/
theorem centralizer_inf_sup_of_disjoint_commutators
    {G : Type*} [Group G] (A B W : Subgroup G)
    (hA : A ≤ normalizer (W : Set G)) (hB : B ≤ normalizer (W : Set G))
    (hBA : B ≤ normalizer (A : Set G)) (hd : Disjoint ⁅A,W⁆ ⁅B,W⁆) :
    (A ⊔ B) ⊓ centralizer (W : Set G) =
      (A ⊓ centralizer (W : Set G)) ⊔ (B ⊓ centralizer (W : Set G)) := by
  let S := normalizer (W : Set G)
  let f := W.normalizerMonoidHom
  have hdis := conjugation_images_disjoint A B W hd
  apply le_antisymm
  · rintro y ⟨hy,hc⟩
    have hmem : y ∈ (A : Set G) * (B : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left A B hBA]
      exact hy
    obtain ⟨a,ha,b,hb,rfl⟩ := hmem
    let a₀ : S := ⟨a,hA ha⟩
    let b₀ : S := ⟨b,hB hb⟩
    have hab : f (a₀*b₀) = 1 := by
      change a₀*b₀ ∈ f.ker
      rw [normalizerMonoidHom_ker]
      exact hc
    have he : f a₀ = (f b₀)⁻¹ := mul_eq_one_iff_eq_inv.mp ((map_mul f a₀ b₀).symm.trans hab)
    have haone : f a₀ = 1 := disjoint_def.mp hdis
      (mem_map_of_mem f ha) (by rw [he]; exact inv_mem (mem_map_of_mem f hb))
    have hbone : f b₀ = 1 := by
      rw [map_mul,haone,one_mul] at hab
      exact hab
    have haC : a ∈ centralizer (W : Set G) := by
      have hh : a₀ ∈ f.ker := haone
      rw [normalizerMonoidHom_ker] at hh
      exact hh
    have hbC : b ∈ centralizer (W : Set G) := by
      have hh : b₀ ∈ f.ker := hbone
      rw [normalizerMonoidHom_ker] at hh
      exact hh
    exact mul_mem_sup ⟨ha,haC⟩ ⟨hb,hbC⟩
  · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)

/-- Disjoint displacement groups make conjugation-image orders multiply. -/
theorem centralizer_relIndex_sup_of_disjoint_commutators
    {G : Type*} [Group G] (A B W : Subgroup G)
    (hA : A ≤ normalizer (W : Set G)) (hB : B ≤ normalizer (W : Set G))
    (hBA : B ≤ normalizer (A : Set G)) (hd : Disjoint ⁅A,W⁆ ⁅B,W⁆) :
    (centralizer (W : Set G)).relIndex (A ⊔ B) =
      (centralizer (W : Set G)).relIndex A * (centralizer (W : Set G)).relIndex B := by
  let S := normalizer (W : Set G)
  let f := W.normalizerMonoidHom
  let A₀ := A.subgroupOf S
  let B₀ := B.subgroupOf S
  have hn₀ : B₀ ≤ normalizer (A₀ : Set S) :=
    (comap_mono hBA).trans (A.le_normalizer_comap S.subtype)
  have hn : B₀.map f ≤ normalizer (A₀.map f : Set (MulAut W)) :=
    (map_mono hn₀).trans (A₀.le_normalizer_map f)
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint (A₀.map f) (B₀.map f) hn
    (conjugation_images_disjoint A B W hd)
  rw [←Subgroup.map_sup,←relIndex_ker,←relIndex_ker,←relIndex_ker,
    normalizerMonoidHom_ker] at hc
  rw [←subgroupOf_sup hA hB,relIndex_subgroupOf (sup_le hA hB),
    relIndex_subgroupOf hA,relIndex_subgroupOf hB] at hc
  exact hc

end Subgroup
