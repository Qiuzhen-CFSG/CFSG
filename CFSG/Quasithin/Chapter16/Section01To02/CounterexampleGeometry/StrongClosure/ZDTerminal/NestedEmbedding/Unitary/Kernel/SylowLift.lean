module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Unitary.Kernel.Setup
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# A Sylow normalizer lift centralizing the terminal action kernel

Let `L` be the normal terminal involution span, `Q = L/O₂′(L)`, and `ρ` the
ambient conjugation action on `Q`. A fixed-point-free normalizer element for
each Sylow two-subgroup of `Q` lifts to an element of `L` normalizing `S ∩ L`
and centralizing the entire subgroup `D = S ∩ ker ρ`.

The restricted kernel is the odd core, so `[L,D]` lies in its ambient image
`O`. Intersecting with `S` shows that `S ∩ L` centralizes `D`. Coprime
centralizer lifting through `G/O` makes `C_L(D) → Q` surjective, with odd
kernel. Coprime normalizer lifting inside this centralizer then supplies the
required element. Centerlessness of `Q` transfers the fixed-point assertion
from `Q` to its actual inner automorphism image.

This is the conditional lifting step in Aschbacher (1975), Lemma 3.4,
printed pp.94–96. Its intrinsic fixed-point-free hypothesis is explicit;
the unitary torus construction is a separate input. The centralizer lifting
used here is Bender–Glauberman, Lemma 1.14.
-/

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

/-- Lift an intrinsic fixed-point-free Sylow normalizer while centralizing
all of the ambient kernel's Sylow intersection. -/
public theorem terminal_sylowNormalizerLift_of_fixedPointFree_normalizers
    (S : Sylow 2 G) {A₁ A₂ : Subgroup G}
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (hrank : TwoRankAtLeastTwo A₁)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hfree : ∀ P : Sylow 2 ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))),
      ∃ d, d ∈ normalizer (P : Set _) ∧ ∀ x ∈ P, Commute d x → x = 1) :
    TerminalSylowNormalizerLift S hL := by
  let L := closure (terminalInvolutions A₁ A₂)
  let : L.Normal := hL
  let O₀ := pPrimeCore 2 L
  let O := O₀.map L.subtype
  let : O.Normal := inferInstanceAs (O₀.map L.subtype).Normal
  let ρ := terminalQuotientAction hL
  let K := ρ.ker
  let D := (S : Subgroup G) ⊓ K
  let C := (centralizer (D : Set G)).subgroupOf L
  let q := QuotientGroup.mk' O₀
  let qG := QuotientGroup.mk' O
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    rw [show Nat.card O = Nat.card O₀ from card_map_of_injective L.subtype_injective]
    exact pPrimeCore_coprime_card
  have hOL : O ≤ L := map_subtype_le _
  have hrestricted : (ρ.comp L.subtype).ker = O₀ :=
    terminalQuotientAction_restrict_ker hL hrank hs
  -- The ambient odd core image is exactly the kernel inside the span.
  have hLK : L ⊓ K = O := by
    ext x
    constructor
    · rintro ⟨hxL, hxK⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      rw [← hrestricted]
      exact hxK
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.property, ?_⟩
      rw [← hrestricted] at hx
      exact hx
  have hcomm (l : G) (hl : l ∈ L) (d : G) (hd : d ∈ D) : ⁅l, d⁆ ∈ O := by
    rw [← hLK]
    exact commutator_le_inf L K (commutator_mem_commutator hl hd.2)
  have hOS : O ⊓ (S : Subgroup G) = ⊥ := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    apply disjoint_iff.mp (disjoint_of_coprime_natCard ?_)
    rw [hn]
    exact hOcop.symm.pow_right n
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal L
  -- The commutators also lie in the Sylow subgroup, hence are trivial.
  have hTC : (T : Subgroup L) ≤ C := by
    intro t ht
    apply mem_centralizer_iff.mpr
    intro d hd
    have htS : (t : G) ∈ (S : Subgroup G) := by
      change t ∈ (S : Subgroup G).subgroupOf L
      rwa [← hT]
    have hcO := hcomm t t.property d hd
    have hcS : ⁅(t : G), d⁆ ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem
        ((S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem htS hd.1)
          ((S : Subgroup G).inv_mem htS)) ((S : Subgroup G).inv_mem hd.1)
    have hc1 : ⁅(t : G), d⁆ = 1 := by
      have hc : ⁅(t : G), d⁆ ∈ O ⊓ (S : Subgroup G) := ⟨hcO, hcS⟩
      simpa only [hOS, mem_bot] using hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp hc1).symm
  let f : C →* L ⧸ O₀ := q.comp C.subtype
  -- Lift a centralizing coset in G/O, then recover membership in L.
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective O₀ y
    have hlcent : qG (l : G) ∈ centralizer (D.map qG : Set (G ⧸ O)) := by
      apply mem_centralizer_iff.mpr
      rintro _ ⟨d, hd, rfl⟩
      have hc : qG ⁅(l : G), d⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr
        (hcomm l l.property d hd)
      have hc' : ⁅qG (l : G), qG d⁆ = 1 := by simpa only [map_commutatorElement] using hc
      exact (commutatorElement_eq_one_iff_mul_comm.mp hc').symm
    let : Fact (IsPGroup 2 D) := ⟨S.isPGroup'.to_le inf_le_left⟩
    rw [centralizer_map_quotient_eq_map_centralizer 2 D O inferInstance hOcop] at hlcent
    obtain ⟨c, hc, hcl⟩ := hlcent
    have hdiff : c * (l : G)⁻¹ ∈ O := by
      apply (QuotientGroup.eq_one_iff _).mp
      change qG (c * (l : G)⁻¹) = 1
      rw [map_mul, map_inv, hcl, mul_inv_cancel]
    have hcL : c ∈ L := by
      have hm := L.mul_mem (hOL hdiff) l.property
      simpa only [inv_mul_cancel_right] using hm
    let cL : L := ⟨c, hcL⟩
    have hdiff₀ : cL * l⁻¹ ∈ O₀ := by
      obtain ⟨a, ha, hea⟩ := hdiff
      have he : a = cL * l⁻¹ := Subtype.ext hea
      exact he ▸ ha
    refine ⟨⟨cL, hc⟩, ?_⟩
    change q cL = q l
    have he : q (cL * l⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hdiff₀
    simpa only [map_mul, map_inv, mul_inv_eq_one] using he
  have hfcop : Nat.Coprime 2 (Nat.card f.ker) := by
    have hk : f.ker = O₀.comap C.subtype := by
      ext c
      exact QuotientGroup.eq_one_iff (c : L)
    rw [hk]
    exact Nat.Coprime.of_dvd_right
      (card_comap_dvd_of_injective O₀ C.subtype C.subtype_injective) pPrimeCore_coprime_card
  -- Lift the intrinsic normalizer element inside C_L(D).
  let U := (T : Subgroup L).subgroupOf C
  have hUmap : U.map C.subtype = (T : Subgroup L) := map_subgroupOf_eq_of_le hTC
  let : Fact (IsPGroup 2 U) := ⟨T.isPGroup'.comap_subtype⟩
  let P := T.mapSurjective (QuotientGroup.mk'_surjective O₀)
  have hUP : U.map f = (P : Subgroup (L ⧸ O₀)) := by
    change U.map (q.comp C.subtype) = (T : Subgroup L).map q
    rw [← map_map, hUmap]
  obtain ⟨d, hdN, hdfree⟩ := hfree P
  have hdmap : d ∈ (normalizer (U : Set C)).map f := by
    rw [← normalizer_map_eq_of_coprime_kernel 2 U f hsurj hfcop, hUP]
    exact hdN
  obtain ⟨g, hgN, hgd⟩ := hdmap
  refine ⟨T, hT, ((g : C) : L), (g : L).property, ?_, g.property, ?_⟩
  · have hg := (U.le_normalizer_map C.subtype) (mem_map_of_mem C.subtype hgN)
    rw [hUmap] at hg
    exact ((T : Subgroup L).le_normalizer_map L.subtype) (mem_map_of_mem L.subtype hg)
  · rintro t ⟨tL, htL, rfl⟩ hgt
    -- Inner conjugation is faithful because the Bender quotient is centerless.
    have hinj : Function.Injective (MulAut.conj : (L ⧸ O₀) →* MulAut (L ⧸ O₀)) := by
      apply (MulAut.conj : (L ⧸ O₀) →* MulAut (L ⧸ O₀)).ker_eq_bot_iff.mp
      apply eq_bot_iff.mpr
      intro z hz
      have hzC : z ∈ center (L ⧸ O₀) := by
        apply mem_center_iff.mpr
        intro x
        have he := DFunLike.congr_fun hz x
        change z * x * z⁻¹ = x at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm
      have hcenter : center (L ⧸ O₀) = ⊥ := terminal_quotient_center_eq_bot hrank hs
      simpa only [hcenter, mem_bot] using hzC
    have hinner : Commute (MulAut.conj d) (MulAut.conj (q tL)) := by
      change Commute (terminalQuotientAction hL ((g : L) : G))
        (terminalQuotientAction hL (tL : G)) at hgt
      rw [terminalQuotientAction_inner hL (g : L), terminalQuotientAction_inner hL tL] at hgt
      change Commute (MulAut.conj (f g)) (MulAut.conj (q tL)) at hgt
      rwa [hgd] at hgt
    have hcom : Commute d (q tL) := Commute.of_map hinj hinner
    have ht1 : q tL = 1 := hdfree (q tL) (mem_map_of_mem q htL) hcom
    exact (terminalQuotientAction_inner hL tL).trans (by
      change MulAut.conj (q tL) = 1
      rw [ht1, map_one])
end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
