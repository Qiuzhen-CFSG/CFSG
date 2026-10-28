module

public import Theory.GroupTheory.ConjugateSpanKernel
public import Theory.GroupTheory.PCoreProduct

/-!
# The two-group kernel in the affine-nine source configuration

A normal kernel meets the cubic two-perfect factor X in its two-core.
The quotient of XT by X is a two-group, so its kernel intersection is a
two-group. Disjoint images of Y and XT then factor the full kernel into
these two intersections. These are ordinary extension arguments; no
classification of extensions or action-image assumption is used here.

Source application: Aschbacher--Smith, 15.4.10, printed p. 1159.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A normal kernel remains a two-group on the join XT when X is
two-perfect with cubic core quotient, T is a two-group, and X is not killed. -/
theorem twoGroup_kernel_on_cubic_residual_join
    (X T C : Subgroup G) [C.Normal]
    (hp : IsPPerfect 2 X) (hcard : Nat.card (X ⧸ pCore 2 X) = 3)
    (hT : IsPGroup 2 T) (hTX : T ≤ normalizer (X : Set G)) (hne : ¬ X ≤ C) :
    IsPGroup 2 (C.subgroupOf (X ⊔ T)) := by
  have hproper : C.subgroupOf X ≠ ⊤ := by
    intro he
    apply hne
    intro x hx
    exact show (⟨x, hx⟩ : X) ∈ C.subgroupOf X from he ▸ mem_top _
  have hcore : C.subgroupOf X ≤ pCore 2 X :=
    normal_le_pCore_of_pPerfect_prime_quotient hp (by rw [hcard]; exact Nat.prime_three)
      (C.subgroupOf X) hproper
  let S := X ⊔ T
  let N := X.subgroupOf S
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer
    (show X ≤ S from le_sup_left)).mpr (sup_le X.le_normalizer hTX)
  have hgen : N ⊔ T.subgroupOf S = ⊤ := by
    rw [← subgroupOf_sup (show X ≤ S from le_sup_left) (show T ≤ S from le_sup_right),
      subgroupOf_self]
  have hquot : IsPGroup 2 (S ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (T.subgroupOf S) hT.comap_subtype hgen
  let q := (QuotientGroup.mk' N).comp (C.subgroupOf S).subtype
  have hk : IsPGroup 2 q.ker := by
    let r : q.ker →* X :=
      (S.subtype.comp ((C.subgroupOf S).subtype.comp q.ker.subtype)).codRestrict X (by
        intro x
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr (x : q.ker) : r x ∈ pCore 2 X := hcore x.val.property
    let r' : q.ker →* pCore 2 X := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 X => (z.val : G)) he
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hk
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

omit [Finite G] in
/-- Disjoint quotient images force the kernel to factor through its two
intersections, so two-group intersections give a two-group kernel. -/
theorem twoGroup_kernel_of_disjoint_supplement_images
    (Y S C : Subgroup G) [Y.Normal] [C.Normal]
    (hgen : Y ⊔ S = ⊤)
    (hdis : Disjoint (Y.map (QuotientGroup.mk' C)) (S.map (QuotientGroup.mk' C)))
    (hY : IsPGroup 2 (Y ⊓ C : Subgroup G)) (hS : IsPGroup 2 (S ⊓ C : Subgroup G)) :
    IsPGroup 2 C := by
  let q := QuotientGroup.mk' C
  have he : C = (Y ⊓ C) ⊔ (S ⊓ C) := by
    apply le_antisymm ?_ (sup_le inf_le_right inf_le_right)
    intro c hc
    obtain ⟨y, hy, s, hs, rfl⟩ := mem_sup_of_normal_left.mp
      (show c ∈ Y ⊔ S by rw [hgen]; exact mem_top c)
    have hprod : q y * q s = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff (N := C) _).mpr hc
    have hqsY : q s ∈ Y.map q := by
      rw [(inv_eq_iff_mul_eq_one.mpr hprod).symm]
      exact (Y.map q).inv_mem (mem_map_of_mem q hy)
    have hqs : q s = 1 := by
      have hh : q s ∈ (Y.map q) ⊓ (S.map q) := ⟨hqsY, mem_map_of_mem q hs⟩
      exact mem_bot.mp ((disjoint_iff.mp hdis) ▸ hh)
    have hsC : s ∈ C := (QuotientGroup.eq_one_iff (N := C) _).mp hqs
    have hyC : y ∈ C := by
      simpa only [mul_inv_cancel_right] using C.mul_mem hc (C.inv_mem hsC)
    exact (mem_sup_of_normal_left.mpr ⟨y, ⟨hy, hyC⟩, s, ⟨hs, hsC⟩, rfl⟩)
  rw [he]
  exact hY.to_sup_of_normal_left hS

end Subgroup
