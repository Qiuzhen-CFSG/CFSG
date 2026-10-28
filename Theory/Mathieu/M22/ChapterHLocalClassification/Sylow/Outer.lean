module
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Inner
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Centralizers

/-!
# Uniqueness of the elementary subgroup of order 32 in the outer M22 Sylow

The image of native M22 has index two in the pair group. Every outer E32
therefore contains an inner E16. The checked inner catalogue places that
subgroup in the intrinsic hexad core or the inner translations. In the
first case its literal centralizer has order sixteen, a contradiction.
In the second case the centralizer is contained in the outer translations,
and equality follows from their common order of thirty-two.

This uses only commutativity of the elementary subgroup being classified;
its normality is not assumed. The index-two normality is solely that of
the actual native M22 image in its pair overgroup.

Source: Aschbacher--Smith H.14.3(1), printed p.397.
-/

public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
namespace Sporadic.Mathieu.M22ChapterH.CompatibleSylow

private theorem elementary_of_injective {G J : Type*} [Group G] [Group J]
    (f : G →* J) (hf : Function.Injective f) (hJ : IsElementaryAbelian 2 J) :
    IsElementaryAbelian 2 G := by
  refine { is_comm := ⟨fun x y => hf ?_⟩, exponent_dvd_p := ?_ }
  · simpa only [map_mul] using hJ.toIsMulCommutative.is_comm.comm (f x) (f y)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply hf
    simpa only [map_pow, map_one] using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hJ.exponent_dvd_p (f x))

private theorem pair_injective : Function.Injective m22ToPairStabilizer :=
  fun _ _ h => m22Embedding_injective (congrArg Subtype.val h)

private theorem inner_index : m22ToPairStabilizer.range.index = 2 := by
  have hc : Nat.card m22ToPairStabilizer.range = 443520 :=
    (Nat.card_congr (MonoidHom.ofInjective pair_injective).toEquiv.symm).trans m22_order
  have h := m22ToPairStabilizer.range.card_mul_index
  rw [hc, m22PairStabilizer_card] at h
  omega

/-- Every outer E32 contains the image of an inner E16. The order-two quotient
is used only for this intersection bound. -/
private theorem contains_inner_card16 (A : Subgroup m22PairStabilizer)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 32)
    (hAS : A ≤ outer.toSubgroup) :
    ∃ E : Subgroup M22, IsElementaryAbelian 2 E ∧ Nat.card E = 16 ∧
      E ≤ inner.toSubgroup ∧ E.map m22ToPairStabilizer ≤ A := by
  let L := m22ToPairStabilizer.range
  let : L.Normal := Subgroup.normal_of_index_eq_two inner_index
  let B : Subgroup A := L.subgroupOf A
  have hBi : B.index ∣ 2 := inner_index ▸ L.relIndex_dvd_index_of_normal A
  have hb := B.card_mul_index
  rw [hc] at hb
  have hbound : 2 ^ 4 ≤ Nat.card B := by
    have hi : B.index ≤ 2 := Nat.le_of_dvd (by decide) hBi
    nlinarith
  let := hA
  obtain ⟨D, hDB, hDc⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card
    Nat.prime_two (IsElementaryAbelian.isPGroup 2 A) hbound
  let C : Subgroup m22PairStabilizer := D.map A.subtype
  have hCA : C ≤ A := Subgroup.map_subtype_le D
  have hCL : C ≤ L := by
    rintro _ ⟨d, hd, rfl⟩
    exact hDB hd
  have hCc : Nat.card C = 16 :=
    (Subgroup.card_map_of_injective A.subtype_injective).trans hDc
  have hD : IsElementaryAbelian 2 D := elementary_of_injective D.subtype D.subtype_injective hA
  let := hD
  have hC : IsElementaryAbelian 2 C := IsElementaryAbelian.map A.subtype
  let E := C.comap m22ToPairStabilizer
  have hE : E.map m22ToPairStabilizer = C := Subgroup.map_comap_eq_self hCL
  let r : E →* C := (m22ToPairStabilizer.comp E.subtype).codRestrict _ (fun x => x.property)
  have hr : Function.Injective r :=
    fun _ _ h => Subtype.ext (pair_injective (congrArg Subtype.val h))
  refine ⟨E, elementary_of_injective r hr hC, ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective (K := E) pair_injective, hE, hCc]
  · intro x hx
    exact hAS (hCA hx)
  · rw [hE]
    exact hCA

/-- The source translation subgroup is the unique E32 of the outer Sylow.
The proof uses the inner catalogue and literal centralizers, without assuming
normality of the elementary subgroup being classified. -/
theorem outer_card32 (A : Subgroup m22PairStabilizer) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 32) (hAS : A ≤ outer.toSubgroup) :
    A = Sextet.outerTranslations := by
  obtain ⟨E, hE, hEc, hES, hEA⟩ := contains_inner_card16 A hA hc hAS
  have hcomm (g : m22PairStabilizer) (hg : g ∈ A) (x : M22) (hx : x ∈ E) :
      g.val * m22Embedding x = m22Embedding x * g.val := by
    have hxa : m22ToPairStabilizer x ∈ A := hEA (Subgroup.mem_map_of_mem _ hx)
    exact congrArg (fun z : A => z.val.val)
      (hA.toIsMulCommutative.is_comm.comm ⟨g, hg⟩ ⟨m22ToPairStabilizer x, hxa⟩)
  rcases inner_card16 E hE hEc hES with he | he
  · have hle : A ≤ m22OuterHexadKernel m22SourceOctad := by
      intro g hg
      exact centralizer_hexad g (hAS hg) (fun x hx => hcomm g hg x (he.symm ▸ hx))
    have hb := Subgroup.card_le_of_le hle
    rw [hc, Hexad.outer_kernel_card] at hb
    omega
  · apply Subgroup.eq_of_le_of_card_ge
    · intro g hg
      exact centralizer_translations g (hAS hg) (fun x hx => hcomm g hg x (he.symm ▸ hx))
    · rw [outerTranslations_card, hc]

end Sporadic.Mathieu.M22ChapterH.CompatibleSylow
