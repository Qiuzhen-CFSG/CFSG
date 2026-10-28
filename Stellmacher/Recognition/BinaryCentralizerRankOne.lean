module

public import Stellmacher.MainDefs
public import Theory.GroupTheory.BinaryWeakCoreSolvableCentralizer
public import Theory.GroupTheory.ElementaryCommutingCoprime
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.ElementaryCommutingOddQuotient
public import Stellmacher.Recognition.BinaryCentralizerRankOneCoreFree

/-!
# Binary commuting-component transport with rank-one centralizer

Let Q be a nontrivial two-subgroup in a finite N₂ group. Its centralizer is
solvable, since it is contained in the two-local normalizer of Q. If the
centralizer contains no elementary four-group, it has a unique involution.
Indeed, a central involution z of Q belongs to the centralizer and commutes
with every element of it; any second involution would generate a four-group
with z.

Work in H = Q C_G(Q), which is solvable because it lies in the two-local
normalizer of Q, and factor out its odd core. The quotient map is injective
on Q and carries its centralizer onto the quotient centralizer. Elementary subgroups lift through odd
kernels, so the rank-one bound survives. The core-free central-product
theorem supplies an elementary eight in the quotient two-core. Odd-quotient
component transport then connects B to each conjugate inside H. Mapping
that path to G and connecting A to B inside S proves the required transport.

Source: the binary simple-group remark following GLS2, Proposition 22.4
(`refs/KGroup/GLS2/ChapterF.tex`). The odd-prime proof displayed there does
not prove the binary case.
-/

namespace Stellmacher.Recognition
open Subgroup

private theorem exists_central_involution
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    ∃ z : G, z ∈ Q ∧ z ∈ centralizer (Q : Set G) ∧ orderOf z = 2 := by
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  let : Nontrivial (center Q) := hQ.center_nontrivial
  have hcenter := hQ.to_subgroup (center Q)
  have hdiv : 2 ∣ Nat.card (center Q) := by
    obtain ⟨n, hn, hcard⟩ := hcenter.nontrivial_iff_card.mp inferInstance
    rw [hcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
  refine ⟨z.val.val, z.val.property, ?_, ?_⟩
  · intro q hq
    exact congrArg (fun x : Q => (x : G))
      ((mem_center_iff.mp z.property) ⟨q, hq⟩)
  · simpa only [orderOf_coe] using hz

/-- The rank-one centralizer in the binary transport problem is solvable and
has a unique involution, supplied by the center of the original two-subgroup. -/
public theorem binaryCentralizerRankOne_structure
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (Q E : Subgroup G) [IsElementaryAbelian 2 E]
    (hQS : Q ≤ S) (hEQ : E ≤ Q) (hE : 4 ≤ Nat.card E)
    (hrank : ∀ F : Subgroup G, F ≤ centralizer (Q : Set G) →
      IsElementaryAbelian 2 F → Nat.card F < 4) :
    Group.IsSolvable (centralizer (Q : Set G)) ∧
      ∃ z : G, z ∈ Q ∧ z ∈ centralizer (Q : Set G) ∧ orderOf z = 2 ∧
        ∀ t : G, t ∈ centralizer (Q : Set G) → orderOf t = 2 → t = z := by
  have hQ : IsPGroup 2 Q := S.isPGroup'.to_le hQS
  have hne : Q ≠ ⊥ := by
    intro hQbot
    have hc := card_le_of_le hEQ
    rw [hQbot, card_bot] at hc
    omega
  have hsolv : Group.IsSolvable (centralizer (Q : Set G)) := by
    let : Group.IsSolvable (normalizer (Q : Set G)) :=
      hN _ ⟨Q, hne, hQ, rfl⟩
    exact Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (centralizer_le_normalizer (Q : Set G)))
  obtain ⟨z, hzQ, hzC, hz⟩ := exists_central_involution Q hQ hne
  refine ⟨hsolv, z, hzQ, hzC, hz, ?_⟩
  intro t htC ht
  by_contra htz
  let F := closure ({z, t} : Set G)
  let : IsKleinFour F := isKleinFour_closure_pair z t
    (by simpa [pow_two, hz] using pow_orderOf_eq_one z)
    (by simpa [pow_two, ht] using pow_orderOf_eq_one t)
    (by intro h; simp [h] at hz)
    (by intro h; simp [h] at ht) (Ne.symm htz) (htC z hzQ)
  have hFe : IsElementaryAbelian 2 F := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by simp }
  have hFC : F ≤ centralizer (Q : Set G) := (closure_le _).mpr (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hzC
    · exact htC)
  have hsmall := hrank F hFC hFe
  rw [IsKleinFour.card_four] at hsmall
  omega

/-- Rank-one binary centralizers preserve the commuting component of a
rank-three elementary subgroup in the chosen Sylow subgroup. The simplicity,
nonsolvability, and rank bound on Q are retained for the campaign interface;
the proof only needs the supplied two-local solvability and the other hypotheses. -/
public theorem binaryCentralizerRankOne_transport
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hG : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A Q E B : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 B]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A) (hQS : Q ≤ S)
    (hEQ : E ≤ Q) (hE : 4 ≤ Nat.card E)
    (hBQC : B ≤ Q ⊔ ((S : Subgroup G) ⊓ centralizer (Q : Set G)))
    (hB : 8 ≤ Nat.card B)
    (hrank : ∀ F : Subgroup G, F ≤ centralizer (Q : Set G) →
      IsElementaryAbelian 2 F → Nat.card F < 4)
    (_hQrank : ∀ D : Subgroup G, D ≤ Q → IsElementaryAbelian 2 D → Nat.card D < 8)
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  let C := centralizer (Q : Set G)
  let H := Q ⊔ C
  have hQ : IsPGroup 2 Q := S.isPGroup'.to_le hQS
  have hQne : Q ≠ ⊥ := by
    intro h
    have hcard := card_le_of_le hEQ
    rw [h, card_bot] at hcard
    omega
  have hHN : H ≤ normalizer (Q : Set G) :=
    sup_le Q.le_normalizer (Subgroup.centralizer_le_normalizer _)
  let : Group.IsSolvable (normalizer (Q : Set G)) := hN _ ⟨Q, hQne, hQ, rfl⟩
  let : Group.IsSolvable H :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hHN)
  have hQH : Q ≤ H := le_sup_left
  have hCH : C ≤ H := le_sup_right
  let QH := Q.subgroupOf H
  have hcentralizer : centralizer (QH : Set H) = C.subgroupOf H := by
    ext x
    constructor
    · intro hx q hq
      exact congrArg Subtype.val (hx ⟨q, hQH hq⟩ hq)
    · intro hx q hq
      exact Subtype.ext (hx (q : G) hq)
  have hgen : QH ⊔ centralizer (QH : Set H) = ⊤ := by
    rw [hcentralizer]
    change Q.subgroupOf H ⊔ C.subgroupOf H = ⊤
    rw [← subgroupOf_sup hQH hCH]
    exact subgroupOf_self H
  have hQHtwo : IsPGroup 2 QH :=
    hQ.of_equiv (subgroupOfEquivOfLe hQH).symm
  have hCrank : ∀ F : Subgroup (centralizer (QH : Set H)),
      IsElementaryAbelian 2 F → Nat.card F < 4 := by
    intro F hF
    let := hF
    let f : centralizer (QH : Set H) →* G :=
      H.subtype.comp (centralizer (QH : Set H)).subtype
    have hf : Function.Injective f :=
      H.subtype_injective.comp (centralizer (QH : Set H)).subtype_injective
    have hFC : F.map f ≤ C := by
      rintro x ⟨y, _, rfl⟩
      exact hcentralizer.le y.property
    have hh := hrank (F.map f) hFC (IsElementaryAbelian.map f)
    rwa [card_map_of_injective hf] at hh
  have hBH : B ≤ H := hBQC.trans (sup_le_sup_left inf_le_right Q)
  let BH := B.subgroupOf H
  let : IsElementaryAbelian 2 BH := IsElementaryAbelian.subgroupOf hBH
  have hBHcard : 8 ≤ Nat.card BH := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv]
    exact hB
  let cH : H := ⟨c, hCH hc⟩
  have hpath := (elementaryCommutingConnected_conj_of_rank_one_centralizer_product
    QH BH hQHtwo hgen hCrank hBHcard cH).map_injective H.subtype H.subtype_injective
  have hBmap : BH.map H.subtype = B := map_subgroupOf_eq_of_le hBH
  have hconj : (BH.map (MulAut.conj cH).toMonoidHom).map H.subtype =
      B.map (MulAut.conj c).toMonoidHom := by
    have hhom : H.subtype.comp (MulAut.conj cH).toMonoidHom =
        (MulAut.conj c).toMonoidHom.comp H.subtype := by
      ext x
      rfl
    rw [map_map, hhom, ← map_map, hBmap]
  rw [hBmap, hconj] at hpath
  have hBS : B ≤ S := hBQC.trans (sup_le hQS inf_le_left)
  have hAB := elementaryCommutingConnected_of_le_twoGroup S A B S.isPGroup' hA hB hAS hBS
  exact hAB.trans (hpath.trans (hAB.symm.map (MulAut.conj c)))

end Stellmacher.Recognition
