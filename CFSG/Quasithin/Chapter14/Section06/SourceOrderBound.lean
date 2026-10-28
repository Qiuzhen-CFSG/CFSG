module
public import CFSG.Quasithin.Chapter14.Section06.SourceF9
public import Theory.GroupTheory.CentralBinaryCommutatorDuality
public import Theory.ElementaryAbelian.BinaryPairingCardinality
public import Theory.ElementaryAbelian.BinaryQuotientRank

/-!
# The order threshold in original 14.6.9

Apply the existing binary commutator duality to the literal O₂(H) and the
H-span of the original plane. The two centralizer quotients have equal order.
The span lies in its own centralizer, and its fixed subgroup contains the
original central line of order two, so |O₂(H)| is at least twice the square
of the quotient order. Quotient rank at least four and |T:O₂(H)| greater
than four therefore give |O₂(H)| ≥ 2⁹ and |T| > 2¹¹.

The logarithmic rank is exactly the dimension of the elementary abelian
quotient by `Subgroup.log_relIndex_eq_quotient_finrank`. This proves the order
conclusion used in the minimal-parabolic and Goldschmidt-triple arguments;
the separate residual-factorization conclusion of 14.6.9 remains to be proved.
Source: Aschbacher–Smith, refs/quasithin.pdf, 14.5.21(1) and 14.6.9,
printed pp.1019 and 1025.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem central_binary_order_bound
    (Q U Z : Subgroup G) [Q.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    (hUQ : U ≤ Q) (hZU : Z ≤ U) (hZ : Z ≤ center G)
    (hcomm : ⁅Q,U⁆ ≤ Z) (hZcard : Nat.card Z = 2) :
    2 * (centralizer (Q : Set G)).relIndex U ^ 2 ≤ Nat.card Q := by
  let C := (centralizer (Q : Set G)).subgroupOf U
  let D := (centralizer (U : Set G)).subgroupOf Q
  obtain ⟨_,e,_,_⟩ := exists_equivariant_central_binary_commutator_duality
    Q U Z (hZU.trans hUQ) hZ hcomm hZcard
  have he : Nat.card (Q ⧸ D) = Nat.card (U ⧸ C) := by
    have hh := Nat.card_congr e.toEquiv
    rw [MonoidHom.binary_dual_card] at hh
    exact hh
  have hC : 2 ≤ Nat.card C := by
    let f : Z → C := fun z => ⟨⟨z,hZU z.property⟩,fun q _ =>
      mem_center_iff.mp (hZ z.property) q⟩
    have hf : Function.Injective f := by
      intro a b hh
      exact Subtype.ext (congrArg (fun c : C => ((c : U) : G)) hh)
    exact hZcard ▸ Nat.card_le_card_of_injective f hf
  have hD : Nat.card U ≤ Nat.card D := by
    let f : U → D := fun u => ⟨⟨u,hUQ u.property⟩,fun v hv =>
      congrArg Subtype.val (mul_comm (⟨v,hv⟩ : U) u)⟩
    have hf : Function.Injective f := by
      intro a b hh
      exact Subtype.ext (congrArg (fun d : D => ((d : Q) : G)) hh)
    exact Nat.card_le_card_of_injective f hf
  have hU := card_eq_card_quotient_mul_card_subgroup C
  have hQ := card_eq_card_quotient_mul_card_subgroup D
  have hc : (centralizer (Q : Set G)).relIndex U = Nat.card (U ⧸ C) :=
    index_eq_card C
  rw [he] at hQ
  rw [hc]
  calc
    2 * Nat.card (U ⧸ C) ^ 2 = Nat.card (U ⧸ C) * (Nat.card (U ⧸ C) * 2) := by ring
    _ ≤ Nat.card (U ⧸ C) * (Nat.card (U ⧸ C) * Nat.card C) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hC)
    _ = Nat.card (U ⧸ C) * Nat.card U := by rw [←hU]
    _ ≤ Nat.card (U ⧸ C) * Nat.card D := Nat.mul_le_mul_left _ hD
    _ = Nat.card Q := hQ.symm

private theorem f9_order_bound
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] :
    2 * (centralizer (D.QH : Set G)).relIndex D.UH ^ 2 ≤ Nat.card D.QH := by
  obtain ⟨hnQ,hnU,hZQ,hZ,hcomm,hcard⟩ := h.duality_inputs
  let := hnQ
  let := hnU
  let := h.duality_elementary (inferInstance : IsElementaryAbelian 2 D.UH)
  have hZU : D.V₁.subgroupOf D.H ≤ D.UH.subgroupOf D.H :=
    comap_mono (h.point_lt.le.trans (le_conjugateSpanBy _ _))
  have hh := central_binary_order_bound (D.QH.subgroupOf D.H)
    (D.UH.subgroupOf D.H) (D.V₁.subgroupOf D.H)
    (comap_mono h.UH_le_QH) hZU hZ hcomm hcard
  have hcent : centralizer (D.QH.subgroupOf D.H : Set D.H) =
      (centralizer (D.QH : Set G)).subgroupOf D.H := by
    ext x
    constructor
    · intro hc q hq
      exact congrArg Subtype.val (hc ⟨q,pCoreIn_le 2 D.H hq⟩ hq)
    · intro hc q hq
      exact Subtype.ext (hc q hq)
  rw [hcent,relIndex_subgroupOf h.UH_le_H] at hh
  have hc := Nat.card_congr (subgroupOfEquivOfLe (pCoreIn_le 2 D.H)).toEquiv
  exact hh.trans_eq hc

open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The first conclusion of original 14.6.9, on the actual centralizer quotient.
The outside intersection I is unnecessary for this numerical conclusion. -/
theorem source_lemma_14_6_9_order
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hindex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    2 ^ 9 ≤ Nat.card (H.pCoreIn 2) ∧ 2 ^ 11 < Nat.card T := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH
  let : IsElementaryAbelian 2 D.UH := h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy D.V D.H).trans h.UH_le_QH)
  have hbound := f9_order_bound h
  have hnonzero : (centralizer (D.QH : Set G)).relIndex D.UH ≠ 0 := by
    intro he
    change 4 ≤ Nat.log 2 ((centralizer (D.QH : Set G)).relIndex D.UH) at hrank
    simp [he] at hrank
  have hlower := Nat.pow_le_of_le_log hnonzero hrank
  have hcore : 2 ^ 9 ≤ Nat.card (H.pCoreIn 2) := by
    change 2 ^ 9 ≤ Nat.card D.QH
    calc
      2 ^ 9 = 2 * (2 ^ 4) ^ 2 := by norm_num
      _ ≤ 2 * (centralizer (D.QH : Set G)).relIndex D.UH ^ 2 :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hlower 2)
      _ ≤ Nat.card D.QH := hbound
  have hproduct := relIndex_mul_relIndex (⊥ : Subgroup G) D.QH (T : Subgroup G)
    bot_le h.QH_le_T
  simp only [relIndex_bot_left] at hproduct
  refine ⟨hcore,?_⟩
  change Nat.card D.QH * D.QH.relIndex (T : Subgroup G) = Nat.card T at hproduct
  change 4 < D.QH.relIndex (T : Subgroup G) at hindex
  change 2 ^ 9 ≤ Nat.card D.QH at hcore
  calc
    2 ^ 11 = 4 * 2 ^ 9 := by norm_num
    _ ≤ 4 * Nat.card D.QH := Nat.mul_le_mul_left 4 hcore
    _ < D.QH.relIndex (T : Subgroup G) * Nat.card D.QH :=
      Nat.mul_lt_mul_of_pos_right hindex (lt_of_lt_of_le (by decide : 0 < 2 ^ 9) hcore)
    _ = Nat.card T := by rw [Nat.mul_comm,hproduct]

end CFSG.Quasithin.Chapter14.Section06
