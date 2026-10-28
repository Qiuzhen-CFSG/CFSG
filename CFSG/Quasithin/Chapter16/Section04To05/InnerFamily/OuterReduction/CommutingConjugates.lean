module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.EmptyCase
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Selection
public import Theory.GroupTheory.TightlyEmbedded.InvolutionGeneration

/-!
# The Sylow-centralizer clause of (+) in 16.4.9

For s = rˡ distinct from r and commuting with r, tight embedding puts s in
N_G(K′). The order-two assertion transported to the component attached to
J = (K′)ˡ puts ⟨r⟩ in Syl₂(N_{K′}(J)). Tight embedding of J then gives
C_{K′}(s) ≤ N_{K′}(J), so restriction proves the asserted Sylow statement.
No prohibition on fusion is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), assertion (+), printed p.1190. We use left conjugation.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_sylow_overgroup {Q H : Subgroup G}
    (hQ : IsPGroup 2 Q) (hQH : Q ≤ H) :
    ∃ S : Subgroup G, SylowIn S H ∧ Q ≤ S := by
  obtain ⟨S, hS⟩ := (hQ.of_equiv (subgroupOfEquivOfLe hQH).symm).exists_le_sylow
  refine ⟨(S : Subgroup H).map H.subtype, ⟨S, rfl⟩, ?_⟩
  rw [← map_subgroupOf_eq_of_le hQH]
  exact map_mono hS

omit [Finite G] in
/-- A relative Sylow subgroup remains Sylow in an intermediate subgroup. -/
theorem SylowIn.restrict {R H Q : Subgroup G} (h : SylowIn R H)
    (hRQ : R ≤ Q) (hQH : Q ≤ H) : SylowIn R Q := by
  obtain ⟨S, hS, hRS⟩ := exists_sylow_overgroup h.isPGroup hRQ
  exact h.maximal hS.isPGroup (hS.le.trans hQH) hRS ▸ hS

private theorem sylow_zpowers_of_order_two {L J : Subgroup G} {r : G}
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hJ : J ∈ delta L)
    (hr : r ∈ J ⊓ normalizer (centralizer (L : Set G) : Set G))
    (hr2 : orderOf r = 2) :
    SylowIn (zpowers r) (J ⊓ normalizer (centralizer (L : Set G) : Set G)) := by
  have hp : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  obtain ⟨S, hS, hrs⟩ := exists_sylow_overgroup hp (zpowers_le.mpr hr)
  have hcard := hsmall J hJ (fun hh => hempty ⟨J, hh⟩) S hS
  have he : zpowers r = S := eq_of_le_of_card_ge hrs
    (by rw [Nat.card_zpowers, hr2, hcard])
  exact he ▸ hS

/-- The normalization and Sylow-centralizer assertions of source (+). -/
theorem IntersectionSetup.commuting_conjugate_sylow_centralizer
    {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty) {r l : G}
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hl : l ∈ L)
    (hcomm : Commute r (MulAut.conj l r)) (hne : MulAut.conj l r ≠ r) :
    MulAut.conj l r ∈ normalizer ((centralizer (L : Set G)).conjBy g : Set G) ∧
      SylowIn (zpowers r) ((centralizer (L : Set G)).conjBy g ⊓
        centralizer ({MulAut.conj l r} : Set G)) := by
  let K' := (centralizer (L : Set G)).conjBy g
  let J := K'.conjBy l
  let L' := (L.conjBy g).conjBy l
  let s := MulAut.conj l r
  have hKt : IsTightlyEmbedded K' := tight_map h.tight (MulAut.conj g)
  have hJt : IsTightlyEmbedded J := tight_map hKt (MulAut.conj l)
  have hrK : r ∈ K' := (h.sylow.le hr).1
  have hsJ : s ∈ J := ⟨r, hrK, rfl⟩
  have hs2 : orderOf s = 2 := ((MulAut.conj l).orderOf_eq r).trans hr2
  have hsN : s ∈ normalizer (centralizer (L : Set G) : Set G) := by
    have hlN : l ∈ normalizer (centralizer (L : Set G) : Set G) := by
      rw [h.normalizers_eq]
      exact L.le_normalizer hl
    exact (normalizer (centralizer (L : Set G) : Set G)).mul_mem
      ((normalizer (centralizer (L : Set G) : Set G)).mul_mem hlN (h.sylow.le hr).2)
      ((normalizer (centralizer (L : Set G) : Set G)).inv_mem hlN)
  have hsnot : s ∉ K' := by
    intro hs
    exact hne (h.sylow.involution_eq_of_commute_of_card_two
      (hsmall _ h.mem_delta (fun hh => hempty ⟨_, hh⟩) R h.sylow)
      hr hr2 ⟨hs, hsN⟩ hs2 hcomm)
  have hsNK : s ∈ normalizer (K' : Set G) :=
    hKt.involution_centralizer_le_normalizer hrK hr2
      (mem_centralizer_singleton_iff.mpr hcomm.eq.symm)
  have hrCJ : r ∈ centralizer ({s} : Set G) :=
    mem_centralizer_singleton_iff.mpr hcomm.eq
  have hCJ : centralizer ({s} : Set G) ≤ normalizer (J : Set G) :=
    hJt.involution_centralizer_le_normalizer hsJ hs2
  have hcentralizer : centralizer (L' : Set G) = J := by
    have hgC : K' = centralizer (L.conjBy g : Set G) :=
      map_centralizer_equiv _ (MulAut.conj g)
    have hlC : (centralizer (L.conjBy g : Set G)).conjBy l =
        centralizer (L' : Set G) := map_centralizer_equiv _ (MulAut.conj l)
    exact ((congrArg (fun Q : Subgroup G => Q.conjBy l) hgC).trans hlC).symm
  have hd : K' ∈ delta L' := by
    refine ⟨⟨l⁻¹, ?_⟩, ?_, ?_⟩
    · rw [hcentralizer]
      exact (conjBy_inv K' l).symm
    · rw [hcentralizer]
      intro he
      exact hsnot (he.symm ▸ hsJ)
    · have hrH : r ∈ K' ⊓ normalizer (centralizer (L' : Set G) : Set G) := by
        rw [hcentralizer]
        exact ⟨hrK, hCJ hrCJ⟩
      have ho : orderOf (⟨r, hrH⟩ : ↥(K' ⊓ normalizer (centralizer (L' : Set G) : Set G))) = 2 :=
        (orderOf_coe _).symm.trans hr2
      exact even_iff_two_dvd.mpr (ho ▸ orderOf_dvd_natCard (⟨r, hrH⟩ :
        ↥(K' ⊓ normalizer (centralizer (L' : Set G) : Set G))))
  have hempty' : ¬ (deltaZero L').Nonempty := by
    intro hh
    exact hempty ((deltaZero_conjBy_nonempty_iff g).mp
      ((deltaZero_conjBy_nonempty_iff l).mp hh))
  have hrel := sylow_zpowers_of_order_two ((hsmall.conjBy g).conjBy l) hempty' hd
    (show r ∈ K' ⊓ normalizer (centralizer (L' : Set G) : Set G) from
      ⟨hrK, hcentralizer ▸ hCJ hrCJ⟩) hr2
  refine ⟨hsNK, hrel.restrict (zpowers_le.mpr ⟨hrK, hrCJ⟩) ?_⟩
  rw [hcentralizer]
  exact inf_le_inf_left K' hCJ

/-- All of (+), with its printed nonidentity product hypothesis. -/
theorem IntersectionSetup.conjugate_product_plus
    {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty) {r l v : G}
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hl : l ∈ L)
    (hv : v ∈ L ⊓ centralizer ({r} : Set G)) (hv1 : v ≠ 1)
    (he : MulAut.conj l r = r * v) :
    MulAut.conj l r ∈ normalizer ((centralizer (L : Set G)).conjBy g : Set G) ∧
      SylowIn (zpowers r) ((centralizer (L : Set G)).conjBy g ⊓
        centralizer ({MulAut.conj l r} : Set G)) ∧ v ∉ L.conjBy g := by
  have hrv : Commute r v := (mem_centralizer_singleton_iff.mp hv.2).symm
  have hcomm : Commute r (MulAut.conj l r) := by
    rw [he]
    exact (Commute.refl r).mul_right hrv
  have hne : MulAut.conj l r ≠ r := by
    intro hh
    exact hv1 (mul_left_cancel (he.symm.trans (hh.trans (mul_one r).symm)))
  obtain ⟨hn, hs⟩ := h.commuting_conjugate_sylow_centralizer hsmall hempty hr hr2 hl hcomm hne
  exact ⟨hn, hs, h.conjugate_involution_product_not_mem_component hsmall hempty
    hr hr2 hl hcomm hne he⟩

end CFSG.Quasithin.Chapter16.Intersections
