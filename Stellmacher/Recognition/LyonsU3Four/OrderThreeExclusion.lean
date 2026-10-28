module

public import Stellmacher.Recognition.LyonsU3Four.ElementOrders
public import Theory.GroupTheory.NormalComplementFusion
public import Theory.GroupTheory.SylowElementConjugacy
public import FeitThompson.BGsection1.Defs
public import Stellmacher.Recognition.LyonsU3Four.NormalizerAction
public import Stellmacher.Recognition.LyonsU3Four.InvolutionCentralizerComplements
public import Glauberman.SuzukiCharacterization
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Exclusion of the order-three automizer case

Lyons's exclusion uses normal two-complements in involution centralizers.
Given those complements, the Sylow normalizer controls element fusion:
first align the squares by normalizer conjugacy, then use fusion within
the centralizer of the common square. A normal complement makes the last
conjugacy a conjugacy within the Sylow subgroup.

The automizer index divides the group order, so index three also forces
three to divide the group order. Under index three, the local normal-complement
theorem supplies the complements above. Glauberman's characterization then
identifies the group as a Suzuki group, whose order is prime to three,
giving the contradiction.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972),
Lemma 1, pp. 372–373, the paragraph beginning “Suppose |K| = 3”.
-/

namespace Stellmacher.Recognition.LyonsU3Four

/-- The center has order four rather than the full Sylow order. -/
public theorem sylow_not_isMulCommutative {G : Type*} [Group G]
    (S : Sylow 2 G) (h : SylowStructure S) : ¬ IsMulCommutative S := by
  intro hc
  have hz := Subgroup.center_eq_top_iff.mpr hc
  have hcard := h.center_card
  rw [hz, Subgroup.card_top, h.card] at hcard
  norm_num at hcard

/-- The elementary-abelian exception in Glauberman's characterization is absent. -/
public theorem sylow_not_isElementaryAbelian {G : Type*} [Group G]
    (S : Sylow 2 G) (h : SylowStructure S) : ¬ IsElementaryAbelian 2 S := by
  intro hE
  exact sylow_not_isMulCommutative S h hE.toIsMulCommutative

/-- Normality of the Sylow would make its nontrivial proper center normal. -/
public theorem sylow_not_normal {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) : ¬ (S : Subgroup G).Normal := by
  intro hn
  apply normalizer_centerImage_ne_top S h
  apply top_le_iff.mp
  rw [← Subgroup.normalizer_eq_top_iff.mpr hn]
  exact normalizer_sylow_le_normalizer_centerImage S

/-- Normal two-complements in the centralizers of the three Sylow involutions
suffice for control of all element fusion by the Sylow normalizer. -/
public theorem normalizer_controls_fusion_of_involution_centralizers
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S)
    (hcomp : ∀ z ∈ centerImage S, z ≠ 1 →
      HasNormalPComplement 2 (Subgroup.centralizer ({z} : Set G)))
    {x y : G} (hx : x ∈ (S : Subgroup G)) (hy : y ∈ (S : Subgroup G))
    (hxy : IsConj x y) :
    ∃ n ∈ Subgroup.normalizer (S : Set G), n * x * n⁻¹ = y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZC : centerImage S ≤ Subgroup.centralizer (S : Set G) :=
    Subgroup.le_centralizer_iff.mp (sylow_le_centralizer_centerImage S)
  have hnorm {u v : G} (hu : u ∈ centerImage S) (hv : v ∈ centerImage S)
      (huv : IsConj u v) :
      ∃ n ∈ Subgroup.normalizer (S : Set G), n⁻¹ * u * n = v := by
    obtain ⟨g, hg⟩ := isConj_iff.mp huv
    obtain ⟨n, hn, he⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer u g⁻¹
      (hZC hu) (by simpa only [inv_inv, hg] using hZC hv)
    exact ⟨n, hn, he.symm.trans (by simpa only [inv_inv] using hg)⟩
  by_cases hx2 : x ^ 2 = 1
  · have hy2 : y ^ 2 = 1 := isConj_one_right.mp (hx2 ▸ hxy.pow 2)
    obtain ⟨n, hn, he⟩ := hnorm
      (involution_mem_centerImage S h hx hx2)
      (involution_mem_centerImage S h hy hy2) hxy
    exact ⟨n⁻¹, (Subgroup.normalizer (S : Set G)).inv_mem hn, by simpa using he⟩
  have hy2 : y ^ 2 ≠ 1 := fun he => hx2 (isConj_one_left.mp (he ▸ hxy.pow 2))
  have hxsq : x ^ 2 ∈ centerImage S :=
    ⟨(⟨x, hx⟩ : S) ^ 2, square_mem_center S h ⟨x, hx⟩, rfl⟩
  have hysq : y ^ 2 ∈ centerImage S :=
    ⟨(⟨y, hy⟩ : S) ^ 2, square_mem_center S h ⟨y, hy⟩, rfl⟩
  obtain ⟨n, hn, hnsq⟩ :=
    hnorm hxsq hysq (hxy.pow 2)
  let a := (MulAut.conj n⁻¹) x
  have haS : a ∈ (S : Subgroup G) := by
    exact (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (S : Set G)).inv_mem hn) x).mp hx
  have hasq : a ^ 2 = y ^ 2 := by
    change ((MulAut.conj n⁻¹) x) ^ 2 = y ^ 2
    rw [← map_pow]
    simpa only [MulAut.conj_apply, inv_inv] using hnsq
  have hay : IsConj a y :=
    (isConj_iff.mpr ⟨n⁻¹, rfl⟩ : IsConj x a).symm.trans hxy
  let C := Subgroup.centralizer ({y ^ 2} : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (Subgroup.mem_centralizer_iff.mp
      (hZC hysq) s hs)
  let T := S.subtype hSC
  let aC : C := ⟨a, hSC haS⟩
  let yC : C := ⟨y, hSC hy⟩
  have hconjC : IsConj aC yC := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hay
    have hgC : g ∈ C := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hgsq : g * y ^ 2 * g⁻¹ = y ^ 2 := by
        rw [← hasq]
        calc
          g * a ^ 2 * g⁻¹ = (g * a * g⁻¹) ^ 2 := map_pow (MulAut.conj g) a 2
          _ = y ^ 2 := by rw [hg]
          _ = a ^ 2 := hasq.symm
      have he := congrArg (fun b : G => b * g) hgsq
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using he
    exact isConj_iff.mpr ⟨⟨g, hgC⟩, Subtype.ext hg⟩
  obtain ⟨N, hN, hcop, hquot⟩ := hcomp (y ^ 2) hysq hy2
  let := hN
  have hinT : IsConj (⟨aC, haS⟩ : T) (⟨yC, hy⟩ : T) :=
    T.isConj_of_isConj_of_normal_pComplement N hcop hquot hconjC
  obtain ⟨t, ht⟩ := isConj_iff.mp hinT
  have htG : (t : C) * aC * (t : C)⁻¹ = yC := congrArg Subtype.val ht
  have htG' : ((t : C) : G) * a * ((t : C) : G)⁻¹ = y := congrArg Subtype.val htG
  refine ⟨((t : C) : G) * n⁻¹,
    (Subgroup.normalizer (S : Set G)).mul_mem
      ((S : Subgroup G).le_normalizer t.property)
      ((Subgroup.normalizer (S : Set G)).inv_mem hn), ?_⟩
  calc
    _ = ((t : C) : G) * a * ((t : C) : G)⁻¹ := by dsimp [a]; group
    _ = y := htG'

/-- The actual automizer index divides the order of the ambient group. -/
public theorem automizerIndex_dvd_card {G : Type*} [Group G] (S : Sylow 2 G) :
    automizerIndex S ∣ Nat.card G := by
  exact (Subgroup.relIndex_dvd_card _ _).trans
    (Subgroup.normalizer (S : Set G)).card_subgroup_dvd_card

/-- Index three forces a factor three in the ambient group order. -/
public theorem three_dvd_card_of_automizerIndex_eq_three
    {G : Type*} [Group G] (S : Sylow 2 G) (hthree : automizerIndex S = 3) :
    3 ∣ Nat.card G := hthree ▸ automizerIndex_dvd_card S

/-- The order-three case of Lyons's Sylow automizer is impossible: the local
complements and fusion control force a Suzuki group, of order prime to three. -/
public theorem automizerIndex_ne_three
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) : automizerIndex S ≠ 3 := by
  intro hthree
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp := involutionCentralizer_hasNormalPComplement_of_automizerIndex_eq_three
    S h hthree
  obtain ⟨m, hm, ⟨e⟩⟩ := Glauberman.SuzukiCharacterization.exists_suzuki_equiv S
    (oddCore_eq_bot S h) (sylow_not_normal S h) (sylow_not_isMulCommutative S h)
    (fun x hx y hy hxy =>
      normalizer_controls_fusion_of_involution_centralizers S h hcomp hx hy hxy)
    (fun x hx hxord => by
      obtain ⟨hx2, hx1⟩ := orderOf_eq_prime_iff.mp hxord
      exact hcomp x (involution_mem_centerImage S h hx hx2) hx1)
  apply (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).2
  rw [← Nat.card_congr e.toEquiv]
  exact three_dvd_card_of_automizerIndex_eq_three S hthree

end Stellmacher.Recognition.LyonsU3Four
