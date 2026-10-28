module

public import Stellmacher.Recognition.Parrott.CentralizerStructure

/-!
# Self-centralization of Parrott's derived subgroup

Under the original involution-centralizer hypotheses, let `H = C_G(z)`
and `J = O₂(H)`. The actual ambient image `E` of `J'` is its own
centralizer in `G`. No simplicity or local-solvability premise on `G` is
needed.

Parrott's first lemma gives `J' = Φ(J) = Z₂(J)`, elementary abelian of
order 32, and `|Z(J)| = 2`. The order-five action on `J/Φ(J)` has no
proper nontrivial invariant subgroup. Apply this to `C_J(J')`: a full
image would make the whole of `J` centralize `J'`, contradicting the
orders of `J'` and `Z(J)`. Thus `C_J(J') = J'`.

The centralizer in `H` of the image of `J'` is normal. If its order were
divisible by five, the quotient would be a two-group, so the supplied
Sylow five-subgroup would centralize `J'`. The original fixed-point
condition would again place `J'` inside `Z(J)`. The centralizer is therefore
a normal two-subgroup and lies in `J`, where the preceding equality
applies. Finally `z ∈ E`, so every element of `C_G(E)` already lies in
`H`; all transfers use the actual subgroup inclusions.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), Lemma 2, p. 673, opening sentence, using Lemma 1 on p. 672.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition

/-- The actual ambient image of the derived two-core is self-centralizing. -/
public theorem parrott_derived_centralizer {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    centralizer (E : Set G) = E := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let E := D.map (H.subtype.comp J.subtype)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨hZmap, _, _, hPhi, hUpper, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  change D = frattini J at hPhi
  change D = Subgroup.upperCentralSeries J 2 at hUpper
  change Nat.card D = 32 at hDcard
  let : IsElementaryAbelian 2 D := hElem
  have hZcard : Nat.card (center J) = 2 := by
    have hc : Nat.card ((center J).map (H.subtype.comp J.subtype)) = Nat.card (center J) :=
      card_map_of_injective (H.subtype_injective.comp J.subtype_injective)
    rw [hZmap, Nat.card_zpowers, h.involution] at hc
    exact hc.symm
  have hZD : center J ≤ D := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      (Subgroup.upperCentralSeries_mono J (show 1 ≤ 2 by decide))
  have hzE : z ∈ E := by
    apply (map_mono hZD (f := H.subtype.comp J.subtype))
    rw [hZmap]
    exact mem_zpowers z
  obtain ⟨hHcard, _⟩ := ParrottCentralizerHypotheses.card_and_solvable z h
  change Nat.card H = 10240 at hHcard
  obtain ⟨P, hP⟩ := h.five_centralizer
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hHcard]
    decide +kernel
  let : MulDistribMulAction P J :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (P : Subgroup H) J
      (Subgroup.le_normalizer_of_normal (H := J))
  let : IsInvariant P J D := isInvariant_of_characteristic D
  let : IsInvariant P J (center J) := isInvariant_of_characteristic (center J)
  let : MulDistribMulAction P (J ⧸ frattini J) :=
    quotientMulDistribMulAction (frattini J) (isInvariant_of_characteristic (frattini J))
  have hfixed : FixedPoints.subgroup P J ≤ center J := by
    intro x hx
    apply hP
    change (x : H) ∈ centralizer (P : Set H)
    rw [mem_centralizer_iff]
    intro a ha
    have hfix := congrArg (fun y : J => (y : H)) (hx ⟨a, ha⟩)
    change a * (x : H) * a⁻¹ = x at hfix
    exact mul_inv_eq_iff_eq_mul.mp hfix
  have hPhi16 : Nat.card (J ⧸ frattini J) = 16 := by
    have hPhicard : Nat.card (frattini J) = 32 := hPhi ▸ hDcard
    have hc := (frattini J).index_mul_card
    change Nat.card (J ⧸ frattini J) * Nat.card (frattini J) = Nat.card J at hc
    rw [hPhicard, h.core_card] at hc
    omega
  have hPhine : FixedPoints.subgroup P (J ⧸ frattini J) ≠ ⊤ := by
    intro htop
    apply (Theory.GroupAction.parrott_quotient_actions pCore_isPGroup h.core_class hPcard hfixed).1
    intro a q
    exact (show q ∈ FixedPoints.subgroup P (J ⧸ frattini J) by rw [htop]; trivial) a
  have hPhifixed := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen
    hPcard hPhi16 hPhine
  have hCJD : centralizer (D : Set J) = D := by
    apply le_antisymm
    · let : IsInvariant P J (centralizer (D : Set J)) := isInvariant_centralizer D
      rcases Theory.GroupAction.invariant_frattini_dichotomy_of_five
        hPcard hPhi16 hPhifixed (centralizer (D : Set J)) with hle | htop
      · exact hle.trans_eq hPhi.symm
      · have hctop : centralizer (D : Set J) = ⊤ := frattini_nongenerating htop
        have hdZ : D ≤ center J := centralizer_eq_top_iff_subset.mp hctop
        have hbound := card_le_of_le hdZ
        rw [hDcard, hZcard] at hbound
        omega
    · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  let C := centralizer (DH : Set H)
  let : DH.Characteristic := inferInstance
  let : C.Normal := Subgroup.normal_centralizer
  have hnotfive : ¬ 5 ∣ Nat.card C := by
    intro hdiv
    have hquotdiv : Nat.card (H ⧸ C) ∣ 2 ^ 11 := by
      obtain ⟨n, hn⟩ := hdiv
      have hc := C.card_mul_index
      change Nat.card C * Nat.card (H ⧸ C) = Nat.card H at hc
      rw [hn, hHcard] at hc
      refine ⟨n, ?_⟩
      norm_num
      nlinarith
    have hquot2 : IsPGroup 2 (H ⧸ C) := IsPGroup.of_card_dvd_pow hquotdiv
    let q := QuotientGroup.mk' C
    have himage : (P : Subgroup H).map q = ⊥ := by
      exact disjoint_self.mp (IsPGroup.disjoint_of_ne 5 2 (by decide) _ _
        (P.isPGroup'.map q) (hquot2.to_subgroup _))
    have hPC : (P : Subgroup H) ≤ C := by
      simpa only [q, QuotientGroup.ker_mk'] using
        (Subgroup.map_eq_bot_iff (P : Subgroup H)).mp himage
    have hdZ : D ≤ center J := by
      intro d hd
      apply hP
      change (d : H) ∈ centralizer (P : Set H)
      intro a ha
      exact (hPC ha (d : H) (mem_map_of_mem J.subtype hd)).symm
    have hbound := card_le_of_le hdZ
    rw [hDcard, hZcard] at hbound
    omega
  have hCdiv : Nat.card C ∣ 2 ^ 11 * 5 := by
    simpa only [hHcard, show 2 ^ 11 * 5 = 10240 by norm_num]
      using C.card_subgroup_dvd_card
  have hCtwo : IsPGroup 2 C := IsPGroup.of_card_dvd_pow
    (((Nat.prime_five.coprime_iff_not_dvd.mpr hnotfive).symm).dvd_of_dvd_mul_right hCdiv)
  have hCJ : C ≤ J := le_sSup ⟨inferInstance, hCtwo⟩
  have hCH : C = DH := by
    apply le_antisymm
    · intro c hc
      let cJ : J := ⟨c, hCJ hc⟩
      have hcD : cJ ∈ D := by
        rw [← hCJD]
        intro d hd
        apply Subtype.ext
        exact hc (d : H) (mem_map_of_mem J.subtype hd)
      exact ⟨cJ, hcD, rfl⟩
    · rintro e ⟨d, hd, rfl⟩ f ⟨b, hb, rfl⟩
      exact congrArg (fun x : J => (x : H)) ((hCJD.ge hd) b hb)
  have hCEH : centralizer (E : Set G) ≤ H := by
    intro g hg
    exact mem_centralizer_singleton_iff.mpr (hg z hzE).symm
  apply le_antisymm
  · intro g hg
    let gH : H := ⟨g, hCEH hg⟩
    have hgC : gH ∈ C := by
      rintro d ⟨x, hx, rfl⟩
      apply Subtype.ext
      exact hg (x : G) (mem_map_of_mem (H.subtype.comp J.subtype) hx)
    have hgDH : gH ∈ DH := hCH ▸ hgC
    obtain ⟨d, hd, hdeq⟩ := hgDH
    exact ⟨d, hd, congrArg (fun x : H => (x : G)) hdeq⟩
  · rintro g ⟨d, hd, rfl⟩ e ⟨b, hb, rfl⟩
    exact congrArg (fun x : J => ((x : H) : G)) ((hCJD.ge hd) b hb)

end Stellmacher.Recognition
