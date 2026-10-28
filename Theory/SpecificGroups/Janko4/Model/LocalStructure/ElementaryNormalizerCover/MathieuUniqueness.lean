module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuBranch
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Native

/-!
# Uniqueness of the native Mathieu kernel

The elementary image and its kernel centralizer have product at most 1024 in
the actual eleven-dimensional action. Thus every elementary subgroup of max1
of order at least 2048 equals its binary kernel. This proves the native
uniqueness used in Kleidman--Wilson (1988), Lemma 1.1.2(i).

If `X ≤ E` and `C(X) ≤ max1`, every conjugate of `E` under `N(X)` lies in
`C(X)`, so uniqueness forces `N(X) ≤ N(E) = max1`. This is the exact Mathieu
normalizer argument in Proposition 2.2.3, after the centralizer placement has
been proved. The final theorem retains the literal maps for a radical whose
normalizer is controlled by such an `X`.
-/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover
open Subgroup SylowCore SylowCore.Transport
open Simplicity.Max1Fusion.QuotientInvolutions
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel Cardinality.max1Subgroup

theorem sylow_elementary_unique (P : Sylow 2 Local) (A : Subgroup P)
    [IsElementaryAbelian 2 A] (hcard : 2048 ≤ Nat.card A) : A = core P := by
  apply eq_of_card_le_of_image_centralizer_bound
  · intro hn
    obtain ⟨g,hg⟩ := exists_alignment P
    let f := alignedHom P g hg
    have hBe : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
    have hBn : A.map f ≠ ⊥ := by
      rw [ne_eq, Subgroup.map_eq_bot_iff, alignedHom_ker]
      exact hn
    let := hBe
    have hc := ElementaryBound.elementary_fixed_bound (A.map f) hBn
    have he := alignedHom_image_card P g hg A
    rw [← he, localKernel_sylow_card]
    exact lt_of_le_of_lt
      ((Nat.mul_le_mul_left _ (centralizer_card_le_fixedMasks P A g hg)).trans hc) (by decide)
  · simpa only [localKernel_sylow_card] using hcard

theorem local_elementary_unique (A : Subgroup max1) [IsElementaryAbelian 2 A]
    (hcard : 2048 ≤ Nat.card A) : A = kernel := by
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let : IsElementaryAbelian 2 (A.subgroupOf P.toSubgroup) :=
    IsElementaryAbelian.subgroupOf hAP
  have hc : Nat.card (A.subgroupOf P.toSubgroup) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv
  have he := sylow_elementary_unique P (A.subgroupOf P.toSubgroup) (by simpa only [hc] using hcard)
  have hm := congrArg (fun U : Subgroup P => U.map P.toSubgroup.subtype) he
  simpa only [map_subgroupOf_eq_of_le hAP, core,
    map_subgroupOf_eq_of_le (localKernel_le_sylow P)] using hm

theorem embedded_elementary_unique (A : Subgroup Model) [IsElementaryAbelian 2 A]
    (hAM : A ≤ max1) (hcard : 2048 ≤ Nat.card A) : A = embeddedKernel := by
  let : IsElementaryAbelian 2 (A.subgroupOf max1) := IsElementaryAbelian.subgroupOf hAM
  have hc : Nat.card (A.subgroupOf max1) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv
  have he := local_elementary_unique (A.subgroupOf max1) (by simpa only [hc] using hcard)
  have hm := congrArg (fun U : Subgroup max1 => U.map max1.subtype) he
  simpa only [map_subgroupOf_eq_of_le hAM] using hm

theorem normalizer_le_mathieu_of_kernel_and_centralizer (X : Subgroup Model)
    (hXE : X ≤ embeddedKernel) (hCX : centralizer (X : Set Model) ≤ max1) :
    normalizer (X : Set Model) ≤ max1 := by
  let : IsElementaryAbelian 2 kernel := localKernel_elementary _ _
  let : IsElementaryAbelian 2 embeddedKernel := IsElementaryAbelian.map max1.subtype
  have hEC : embeddedKernel ≤ centralizer (X : Set Model) :=
    embeddedKernel.le_centralizer.trans (centralizer_le hXE)
  intro g hg
  have hgC := normalizer_le_normalizer_centralizer X hg
  have heC := mem_normalizer_iff_map_conj_eq.mp hgC
  let A := embeddedKernel.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hAC : A ≤ centralizer (X : Set Model) := by
    rw [← heC]
    exact Subgroup.map_mono hEC
  have hcard : Nat.card A = 2048 := by
    rw [card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective max1.subtype_injective, Cardinality.localKernel_card]
  have he := embedded_elementary_unique A (hAC.trans hCX) hcard.ge
  have hgE := mem_normalizer_iff_map_conj_eq.mpr he
  simpa only [embedded_localKernel_normalizer_eq_max1] using hgE

/-- Literal radical restriction in the Mathieu branch. The centralizer placement
is the source premise discharged by the preceding native configuration analysis. -/
theorem radical_mathieu_local_of_kernel_and_centralizer
    (P X : Subgroup Model) (hP : P.IsPRadical 2)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (hXE : X ≤ embeddedKernel) (hCX : centralizer (X : Set Model) ≤ max1) :
    normalizer (P : Set Model) ≤ max1 ∧ P ≤ max1 ∧
      (normalizer (P.subgroupOf max1 : Set max1)).map max1.subtype =
        normalizer (P : Set Model) ∧
      (P.subgroupOf max1).IsPRadical 2 ∧
      (normalizer (P.subgroupOf max1 : Set max1)).pCoreIn 2 = P.subgroupOf max1 ∧
      ((normalizer (P.subgroupOf max1 : Set max1)).pCoreIn 2).map max1.subtype = P := by
  have hNM := hNX.trans (normalizer_le_mathieu_of_kernel_and_centralizer X hXE hCX)
  have hPM := P.le_normalizer.trans hNM
  have hNN := hNM.trans max1.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf max1 hPM hNN
  refine ⟨hNM, hPM, ?_, hP.subgroupOf_of_normalizer_normalizes max1 hPM hNN, hcore, ?_⟩
  · rw [← subgroupOf_normalizer_eq hPM, map_subgroupOf_eq_of_le hNM]
  · rw [hcore, map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.ElementaryNormalizerCover
