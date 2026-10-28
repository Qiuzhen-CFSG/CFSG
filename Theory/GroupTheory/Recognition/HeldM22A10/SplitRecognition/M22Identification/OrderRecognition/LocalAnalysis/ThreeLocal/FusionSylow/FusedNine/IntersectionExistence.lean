module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.AmbientElementary
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Geometry

/-!
# An order-three element normalizing both elementary sixteens

The coordinate calculation gives `|E ∩ F| = 4`. Consequently the image of
`F` in the genuine quotient `N(E)/E ≃ A₆` is a four-group, and its full
preimage is `EF`. Every four-group normalizer in A₆ has order divisible by
three: transport an explicit order-three normalizing permutation along an
actual automorphism carrying the marked four-group to the given one.
Cauchy's theorem therefore gives an order-three element in the preimage
of this normalizer. It preserves E and EF. Its conjugate of F is an
elementary sixteen inside EF, hence inside the coordinate Sylow two-group;
the classification of these sixteens forces that conjugate to be F.

Only the involution-normalizer data are assumed. No ambient Sylow-three,
three-fusion, group-order or recognition conclusion enters the argument.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, printed p.8, paragraph preceding Lemma 8.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy

private theorem a6_four_normalizer_three (H : Subgroup AlternatingSix.ShadowLocal.A6) [IsKleinFour H] :
    3 ∣ Nat.card (normalizer (H : Set AlternatingSix.ShadowLocal.A6)) := by
  classical
  obtain ⟨α, rfl⟩ := AlternatingSix.ShadowLocal.FourNormalizers.exists_map_standardFour H
  rw [← map_equiv_normalizer_eq, card_map_of_injective α.injective]
  have h : ∃ n : AlternatingSix.ShadowLocal.A6,
      (∀ i : AlternatingSix.ShadowLocal.FourNormalizers.V,
        ∃ j : AlternatingSix.ShadowLocal.FourNormalizers.V,
          AlternatingSix.ShadowLocal.FourNormalizers.standardEmbedding j =
            n * AlternatingSix.ShadowLocal.FourNormalizers.standardEmbedding i * n⁻¹) ∧
      n ^ 3 = 1 ∧ n ≠ 1 := by decide +kernel
  obtain ⟨n, hn, hn3, hn1⟩ := h
  have hnN : n ∈ normalizer
      (AlternatingSix.ShadowLocal.FourNormalizers.standardFour : Set AlternatingSix.ShadowLocal.A6) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (AlternatingSix.ShadowLocal.FourNormalizers.map_standard_eq_iff (MulAut.conj n)).mpr hn
  let nN : normalizer
      (AlternatingSix.ShadowLocal.FourNormalizers.standardFour : Set AlternatingSix.ShadowLocal.A6) := ⟨n, hnN⟩
  have ho : orderOf nN = 3 := by
    rw [← orderOf_coe nN]
    exact orderOf_eq_prime hn3 hn1
  exact ho ▸ orderOf_dvd_natCard nN

namespace CaseII.IntersectionExistence
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance : DecidablePred (· ∈ modelE) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))
local instance : DecidablePred (· ∈ modelF) := fun x =>
  decidable_of_iff (x * d = d * x) mem_centralizer_singleton_iff.symm

local instance : DecidablePred (· ∈ (modelE ⊓ modelF : Subgroup TwistedModel)) := fun x =>
  inferInstanceAs (Decidable (x ∈ modelE ∧ x ∈ modelF))

private theorem model_intersection_card : Nat.card (modelE ⊓ modelF : Subgroup TwistedModel) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
private theorem intersection_card : Nat.card (E D k ⊓ F D k : Subgroup G) = 4 := by
  rw [← modelE_map D k, ← modelF_map D k, ← map_inf _ _ _ (into_injective D k),
    card_map_of_injective (into_injective D k)]
  exact model_intersection_card

omit [Finite G] in
private theorem E_ne_F : E D k ≠ F D k := by
  intro he
  have hc := intersection_card D k
  rw [he, inf_idem, F_card D k] at hc
  contradiction

private theorem normalizes_F_of_sup (x : G)
    (hxE : x ∈ normalizer (E D k : Set G))
    (hxJ : x ∈ normalizer ((E D k ⊔ F D k : Subgroup G) : Set G)) :
    x ∈ normalizer (F D k : Set G) := by
  let f := (MulAut.conj x).toMonoidHom
  have hE : (E D k).map f = E D k := mem_normalizer_iff_map_conj_eq.mp hxE
  have hJ : (E D k ⊔ F D k).map f = E D k ⊔ F D k :=
    mem_normalizer_iff_map_conj_eq.mp hxJ
  have hFT : (F D k).map f ≤ caseIISylow D k :=
    ((map_mono (show F D k ≤ E D k ⊔ F D k from le_sup_right)).trans_eq hJ).trans
      (sup_le (E_le_caseIISylow D k) (F_le_caseIISylow D k))
  let := F_elementary D k
  have hc : Nat.card ((F D k).map f) = 16 := by
    rw [card_map_of_injective (MulAut.conj x).injective, F_card D k]
  rcases elementary_sixteen_in_caseIISylow D k ((F D k).map f) hFT
    (IsElementaryAbelian.map f) hc with he | hf
  · exact (E_ne_F D k ((map_injective (MulAut.conj x).injective) (hE.trans he.symm))).elim
  · exact mem_normalizer_iff_map_conj_eq.mpr hf

end CaseII.IntersectionExistence

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The intersection of the two elementary normalizers contains an element
of order three, as required for Janko's choice of Q*. -/
public theorem exists_three_in_normalizer_intersection
    (h2 : InvolutionNormalizerData D k) :
    ∃ x : G, x ∈ normalizer (CaseII.E D k : Set G) ∧
      x ∈ normalizer (CaseII.F D k : Set G) ∧ orderOf x = 3 := by
  classical
  let N := normalizer (CaseII.E D k : Set G)
  let B := (CaseII.E D k).subgroupOf N
  let C := (CaseII.F D k).subgroupOf N
  have hEN : CaseII.E D k ≤ N := le_normalizer
  have hFN : CaseII.F D k ≤ N :=
    (CaseII.F_le_caseIISylow D k).trans (CaseII.caseIISylow_le_normalizer_E D k)
  obtain ⟨K, hK, ⟨eK⟩⟩ := h2.normalizer_E
  let e : N ⧸ B ≃* alternatingGroup (Fin 6) := hK.symm.QuotientMulEquiv.trans eK
  let f : N →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' B)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective B)
  have hker : f.ker = B := by
    ext x
    change e (QuotientGroup.mk' B x) = 1 ↔ x ∈ B
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let H := C.map f
  have hCcard : Nat.card C = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFN).toEquiv]
    exact CaseII.F_card D k
  have hBCcard : Nat.card (B.subgroupOf C) = 4 := by
    rw [← inf_subgroupOf_right B C,
      Nat.card_congr (subgroupOfEquivOfLe (show B ⊓ C ≤ C from inf_le_right)).toEquiv]
    have heq : B ⊓ C = (CaseII.E D k ⊓ CaseII.F D k).subgroupOf N := rfl
    rw [heq, Nat.card_congr (subgroupOfEquivOfLe
      (show CaseII.E D k ⊓ CaseII.F D k ≤ N from inf_le_left.trans hEN)).toEquiv]
    exact CaseII.IntersectionExistence.intersection_card D k
  have hHcard : Nat.card H = 4 := by
    have hi := relIndex_ker C f
    rw [hker] at hi
    have hm := (B.subgroupOf C).card_mul_index
    change Nat.card (B.subgroupOf C) * B.relIndex C = Nat.card C at hm
    rw [hi, hBCcard, hCcard] at hm
    change 4 * Nat.card H = 16 at hm
    omega
  let : IsElementaryAbelian 2 (CaseII.F D k) := CaseII.F_elementary D k
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf hFN
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.map f
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour H := ⟨hHcard, IsElementaryAbelian.exponent_eq_prime⟩
  have hthree : 3 ∣ Nat.card (normalizer (H : Set (alternatingGroup (Fin 6)))) :=
    a6_four_normalizer_three H
  let L := (normalizer (H : Set (alternatingGroup (Fin 6)))).comap f
  have hLmap : L.map f = normalizer (H : Set (alternatingGroup (Fin 6))) :=
    map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top)
  have hLthree : 3 ∣ Nat.card L := by
    have hd := card_map_dvd L f
    rw [hLmap] at hd
    exact hthree.trans hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 hLthree
  have hpre : H.comap f = (CaseII.E D k ⊔ CaseII.F D k).subgroupOf N := by
    change (C.map f).comap f = _
    rw [comap_map_eq, hker, sup_comm, subgroupOf_sup hEN hFN]
  have hxpre : (x : N) ∈ normalizer (H.comap f : Set N) := by
    rw [← comap_normalizer_eq_of_surjective H hf]
    exact x.property
  have hJmap : (H.comap f).map N.subtype = CaseII.E D k ⊔ CaseII.F D k := by
    rw [hpre, map_subgroupOf_eq_of_le (sup_le hEN hFN)]
  have hxJ : ((x : N) : G) ∈ normalizer ((CaseII.E D k ⊔ CaseII.F D k : Subgroup G) : Set G) := by
    rw [← hJmap]
    exact (le_normalizer_map N.subtype) (mem_map_of_mem N.subtype hxpre)
  refine ⟨((x : N) : G), (x : N).property,
    CaseII.IntersectionExistence.normalizes_F_of_sup D k _ (x : N).property hxJ, ?_⟩
  rw [orderOf_coe, orderOf_coe]
  exact hx

end Theory.GroupTheory.HeldM22A10.M22Identification
