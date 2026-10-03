module

public import Theory.GroupTheory.RankOneCentralizerCore
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.ElementaryCommutingOddQuotient
public import Theory.GroupTheory.SolvableNormalSup

/-!
# Solvable rank-one centralizer transport

In a solvable product of a two-subgroup and its rank-one centralizer, pass to
the quotient by the odd core. Fitting theory and quaternion-core transfer
supply an elementary eight in the quotient two-core. Odd-quotient transport
then preserves the elementary commuting component. Applying this inside
`Q C_G(Q)` and connecting the weak-rank witness to `A` inside `S` gives the
ambient transport theorem for a solvable centralizer with a unique involution.

Source: the binary remark following GLS2, Proposition 22.4
(`refs/KGroup/GLS2/ChapterF.tex`), extracted from the solvable Fitting/quaternion
argument in `Stellmacher/Recognition/BinaryCentralizerRankOne.lean`.
-/

namespace Subgroup

/-- Conjugation in a solvable centralizer product preserves the component of
an elementary subgroup of order at least eight when the centralizer has no
elementary four-group. -/
public theorem elementaryCommutingConnected_conj_of_rank_one_centralizer_product
    {H : Type*} [Group H] [Finite H] [Group.IsSolvable H]
    (Q B : Subgroup H) (hQ : IsPGroup 2 Q)
    (hgen : Q ⊔ centralizer (Q : Set H) = ⊤)
    (hrank : ∀ F : Subgroup (centralizer (Q : Set H)),
      IsElementaryAbelian 2 F → Nat.card F < 4)
    [IsElementaryAbelian 2 B] (hB : 8 ≤ Nat.card B) (g : H) :
    ElementaryCommutingConnected 2 B (B.map (MulAut.conj g).toMonoidHom) := by
  let : Q.Normal := normal_of_centralizing_sup_eq_top Q _ hgen le_rfl
  let N := pPrimeCore 2 H
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hker : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact pPrimeCore_coprime_card
  let C := centralizer (Q : Set H)
  let Cbar := C.map q
  have hCbar : Cbar = centralizer (Q.map q : Set (H ⧸ N)) :=
    map_centralizer_eq_of_surjective_coprime q hq hker Q hQ
  let : Cbar.Normal := Normal.map inferInstance q hq
  let f : C →* Cbar := q.subgroupMap C
  have hfker : f.ker = N.subgroupOf C := by
    ext x
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := N) (x : H)).mp
        (congrArg Subtype.val (show f x = 1 from hx))
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := N) (x : H)).mpr hx
  have hfcard : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hfker]
    exact Nat.Coprime.of_dvd_right
      (card_comap_dvd_of_injective N C.subtype C.subtype_injective)
      pPrimeCore_coprime_card
  have hCrank : ∀ F : Subgroup Cbar, IsElementaryAbelian 2 F → Nat.card F < 4 := by
    intro F hF
    let := hF
    obtain ⟨D, hD, _, hcard⟩ :=
      exists_elementaryAbelian_map_eq_of_surjective_coprime f
        (q.subgroupMap_surjective C) hfcard F
    rw [← hcard]
    exact hrank D hD
  have hCcore : pPrimeCore 2 Cbar = ⊥ := by
    have hmap : (pPrimeCore 2 Cbar).map Cbar.subtype = ⊥ :=
      pPrimeCore_eq_bot_iff.mp (pPrimeCore_quotient_pPrimeCore_eq_bot 2) _ inferInstance
        (Nat.Coprime.of_dvd_right (card_map_dvd _ Cbar.subtype) pPrimeCore_coprime_card)
    exact map_injective Cbar.subtype_injective (by simpa only [Subgroup.map_bot] using hmap)
  have hgenbar : Q.map q ⊔ Cbar = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective q hq]
  let : IsElementaryAbelian 2 (B.map q) := IsElementaryAbelian.map q
  have hBcard : 8 ≤ Nat.card (B.map q) := by
    let e := MulEquiv.ofBijective (q.subgroupMap B) ⟨by
      intro x y h
      exact injective_comp_subtype_of_coprime_ker q hker B
        (IsElementaryAbelian.isPGroup 2 B) (congrArg Subtype.val h),
        q.subgroupMap_surjective B⟩
    rw [← Nat.card_congr e.toEquiv]
    exact hB
  rw [hCbar] at hCrank hCcore hgenbar
  obtain ⟨D, hDcore, hD, hDcard⟩ :=
    exists_elementary_eight_le_pCore_of_rank_one_centralizer
      (Q.map q) (B.map q) (hQ.map q) hgenbar hCcore hCrank inferInstance hBcard
  let := hD
  exact elementaryCommutingConnected_conj_of_normal_odd_quotient N B
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hB (pCore 2 (H ⧸ N)) D
    pCore_isPGroup hDcard hDcore g

/-- A solvable centralizer with a unique involution preserves the binary
commuting component whenever its local product contains an elementary eight. -/
public theorem elementaryCommutingConnected_conj_of_solvable_centralizer_unique_involution
    {G : Type*} [Group G] [Finite G] (S A Q B : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S)
    (hBQC : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hsolv : Group.IsSolvable (centralizer (Q : Set G)))
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2)
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  let C := centralizer (Q : Set G)
  let H := Q ⊔ C
  let : Group.IsSolvable C := hsolv
  have hrank : ∀ F : Subgroup G, F ≤ C → IsElementaryAbelian 2 F →
      Nat.card F < 4 := by
    intro F hFC hF
    let := hF
    let : IsElementaryAbelian 2 (F.subgroupOf C) := IsElementaryAbelian.subgroupOf hFC
    have hcard := card_elementary_le_two_of_unique_involution hunique (F.subgroupOf C)
    rw [Nat.card_congr (subgroupOfEquivOfLe hFC).toEquiv] at hcard
    omega
  have hQ : IsPGroup 2 Q := hS.to_le hQS
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
  let : QH.Normal := normal_of_centralizing_sup_eq_top QH _ hgen le_rfl
  let : Group.IsNilpotent QH := hQHtwo.isNilpotent
  let : Group.IsSolvable (C.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hCH).toMonoidHom) (subgroupOfEquivOfLe hCH).injective
  let : Group.IsSolvable (centralizer (QH : Set H)) := by
    rw [hcentralizer]
    infer_instance
  let : Group.IsSolvable H := Group.isSolvable_of_normal_sup_eq_top QH _ hgen
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
  have hAB := elementaryCommutingConnected_of_le_twoGroup S A B hS hA hB hAS hBS
  exact hAB.trans (hpath.trans (hAB.symm.map (MulAut.conj c)))

end Subgroup
