module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalBasic
public import BenderSuzuki.SE.Borel

/-!
# A nonidentity local seed for the ZD centralizer choice

The square-one element in the ZD structural conclusion is central modulo the
odd core, since its image commutes with the derived factor and generates the
quotient together with that factor. If the element were trivial, the derived
factor would be the whole quotient. The relative Borel then becomes an actual
Borel of this simple Bender quotient. Its normal Sylow 2-subgroup acts regularly
on the other cosets, so no involution belongs to two distinct conjugates.
Strong embedding lifts through the odd kernel, contradicting the local input.

Source: GLS, Volume 4, Chapter 2, (4D)--(4E), and Lemma 4.7(a).
-/

namespace BenderSuzuki.ZD

open PFAppendixIII PFchapter1section1 Theory.GroupTheory

private theorem borel_intersection_control
    {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : IsBorelSubgroup B) (hmodel : IsSimpleBenderGroup G)
    {g x : G} (hg : g ∉ B) (hxB : x ∈ B)
    (hxg : x ∈ rightConjugate B g) (hx : IsInvolution x) : False := by
  obtain ⟨P, hPn, hreg⟩ := simpleBender_borel_normalSylow_regular hB hmodel
  let : (P : Subgroup B).Normal := hPn
  let t : B := ⟨x, hxB⟩
  have ht : IsInvolution t := BenderSuzuki.IsInvolution.subtype hx hxB
  have hcyc := isPGroup_zpowers_of_involution ht
  have hle : Subgroup.zpowers t ≤ (P : Subgroup B) := by
    have hh := hcyc.inf_normalizer_sylow P
    change Subgroup.zpowers t ⊓ Subgroup.normalizer ((P : Subgroup B) : Set B) = _ at hh
    rw [Subgroup.normalizer_eq_top, inf_top_eq] at hh
    exact hh.le.trans inf_le_right
  have hxP : x ∈ (P : Subgroup B).map B.subtype :=
    ⟨t, hle (Subgroup.mem_zpowers t), rfl⟩
  let a : G ⧸ B := QuotientGroup.mk g⁻¹
  have ha : a ≠ QuotientGroup.mk 1 := by
    intro he
    have hh := QuotientGroup.eq.mp he
    exact hg (by simpa using hh)
  have hfix : x • a = a := by
    change QuotientGroup.mk (x * g⁻¹) = (QuotientGroup.mk g⁻¹ : G ⧸ B)
    apply QuotientGroup.eq.mpr
    have hh := rightConjugateElem_mem_of_mem_rightConjugate
      (g := g⁻¹) (by simpa using hxg)
    have hh' : g * x * g⁻¹ ∈ B := by
      simpa only [rightConjugateElem, inv_inv] using hh
    convert B.inv_mem hh' using 1
    group
  obtain ⟨_r, _hr, huniq⟩ := hreg ha ha
  have he : (⟨x, hxP⟩ : (P : Subgroup B).map B.subtype) = 1 :=
    (huniq _ hfix).trans (huniq 1 (one_smul G a)).symm
  exact hx.ne_one (congrArg Subtype.val he)

private theorem seed_involution_quotient {G : Type*} [Group G] [Finite G]
    (O : Subgroup G) [O.Normal] (hodd : Odd (Nat.card O))
    {x : G} (hx : IsInvolution x) : IsInvolution (QuotientGroup.mk' O x) := by
  refine ⟨?_, by rw [← map_pow, hx.sq_eq_one, map_one]⟩
  intro he
  have hxO := (QuotientGroup.eq_one_iff x).mp he
  have hxi := BenderSuzuki.IsInvolution.subtype hx hxO
  exact hodd.not_two_dvd_nat
    ((orderOf_eq_prime hxi.sq_eq_one hxi.ne_one) ▸ orderOf_dvd_natCard (⟨x, hxO⟩ : O))

private theorem seed_stronglyEmbedded_of_borel_quotient
    {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hproper : A ≠ ⊤) (hinv : ∃ x ∈ A, IsInvolution x)
    (O : Subgroup G) [O.Normal] (hodd : Odd (Nat.card O)) (hOA : O ≤ A)
    (hmodel : IsSimpleBenderGroup (G ⧸ O))
    (hB : IsBorelSubgroup (A.map (QuotientGroup.mk' O))) :
    IsStronglyEmbedded A := by
  let q := QuotientGroup.mk' O
  have hcomap : (A.map q).comap q = A :=
    Subgroup.comap_map_eq_self (by simpa only [q, QuotientGroup.ker_mk'] using hOA)
  have hBE : IsStronglyEmbedded (A.map q) := by
    refine ⟨?_, ?_, ?_⟩
    · intro htop
      apply hproper
      rw [← hcomap, htop, Subgroup.comap_top]
    · obtain ⟨x, hxA, hx⟩ := hinv
      exact ⟨q x, Subgroup.mem_map_of_mem q hxA, seed_involution_quotient O hodd hx⟩
    · intro g hg x hxB hxg hx
      exact borel_intersection_control hB hmodel hg hxB hxg hx
  refine ⟨hproper, hinv, ?_⟩
  intro g hg x hxA hxg hx
  apply hBE.2.2 (g := q g) (x := q x)
  · intro hh
    exact hg (hcomap ▸ hh)
  · exact Subgroup.mem_map_of_mem q hxA
  · rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hxg ⊢
    obtain ⟨y, hy, he⟩ := hxg
    refine ⟨q y, Subgroup.mem_map_of_mem q hy, ?_⟩
    simpa using congrArg q he
  · exact seed_involution_quotient O hodd hx

/-- Failure of local strong embedding makes the central square-one factor in
`StructureConclusion` nontrivial. This is the seed needed for the centralizer
replacement in GLS Lemma 4.7(a), without any simplicity hypothesis on `K`. -/
public theorem local_structure_central_involution_seed
    {K : Type*} [Group K] [Finite K] {W : Set K} {N : Subgroup K}
    (hp : IsProductDisconnected W N) (hs : StructureConclusion W N)
    (hnot : ¬ IsStronglyEmbedded (N.comap (Subgroup.closure W).subtype)) :
    ∃ u : Subgroup.closure W, IsInvolution u ∧ (u : K) ∈ N ∧
      QuotientGroup.mk' (pPrimeCore 2 (Subgroup.closure W)) u ∈
        Subgroup.center ((Subgroup.closure W) ⧸ pPrimeCore 2 (Subgroup.closure W)) ∧
      pPrimeCore 2 (Subgroup.closure W) ≤ N.comap (Subgroup.closure W).subtype := by
  let L := Subgroup.closure W
  let A := N.comap L.subtype
  let O := pPrimeCore 2 L
  let Q := L ⧸ O
  let q := QuotientGroup.mk' O
  let X := commutator Q
  obtain ⟨u, huN, hu2, hgenL, hgenQ, _hdis, hcomm, hmodel, hOA, hB, _hW⟩ := hs
  have hO : O ≤ A := hOA.trans inf_le_left
  have hcent : q u ∈ Subgroup.center Q := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hy : y ∈ X ⊔ Subgroup.zpowers (q u) := hgenQ ▸ Subgroup.mem_top y
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have haC := hcomm a ha (q u) (Subgroup.mem_zpowers (q u))
    obtain ⟨n, rfl⟩ := hb
    exact (haC.mul_left ((Commute.refl (q u)).zpow_left n)).eq
  have hne : u ≠ 1 := by
    intro hu1
    have hL : commutator L = ⊤ := by simpa [hu1] using hgenL
    have hX : X = ⊤ := by simpa [q, hu1] using hgenQ
    let e : X ≃* Q := MulEquiv.ofBijective X.subtype
      ⟨Subtype.val_injective, fun y => ⟨⟨y, hX ▸ Subgroup.mem_top y⟩, rfl⟩⟩
    have hmodelQ : IsSimpleBenderGroup Q := hmodel.map_mulEquiv e
    have hB' : IsBorelSubgroup (A.map q) := by
      have hh := hB.map_mulEquiv e
      have he : (((A ⊓ commutator L).map q).subgroupOf X).map e.toMonoidHom = A.map q := by
        rw [hL, inf_top_eq]
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact hz
        · intro hy
          exact ⟨⟨y, hX ▸ Subgroup.mem_top y⟩, hy, rfl⟩
      rw [he] at hh
      exact hh
    apply hnot
    have hpL := productDisconnected_closure hp
    apply seed_stronglyEmbedded_of_borel_quotient hpL.proper _ O
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hO hmodelQ hB'
    obtain ⟨x, hx, hxA⟩ := hpL.nonempty
    exact ⟨x, hxA, hpL.involutions x hx⟩
  exact ⟨u, ⟨hne, hu2⟩, huN, hcent, hO⟩

end BenderSuzuki.ZD
