module

public import Stellmacher.Recognition.Parrott.SecondCentralizerTransferSetup
public import Stellmacher.Recognition.Parrott.NormalizerInvolutionCosets

/-!
# Geometry of the second transfer kernel

Write W for the ambient image of Ω₁(O₂(N_G(F))). An invariant subgroup
Y of order 128 excluding the supplied fixed root b has Ω₁(Y)=F and
Z(Y)=Z(W), with all subgroups embedded by their actual inclusions.

Since Y has index two in W, it contains b²=v. Orbit counting under the
supplied group Q of order three forces F∩Y to have order 32. Any involution
of Y outside F can be moved by Q into E\F. Together with E∩F it generates
E, after which involution transport forces all of W into Y, a contradiction.
Finally Z(W)≤Z(Y)≤F; orbit counting excludes center order sixteen, and
C_G(F)=F excludes center order 32. Thus Z(Y)=Z(W).

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§4, pp.682–683. This gives the omega and center calculations for the
source's subgroup ⟨F,bw,by⟩ without selecting new generator witnesses.
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Every invariant subgroup of index two in omega contains F if it contains
 the prescribed fixed involution. -/
public theorem second_transfer_invariant_subgroup_contains_elementary
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let A := (Q : Subgroup N).map N.subtype
    ∀ Y : Subgroup G, Y ≤ W → Nat.card Y = 128 →
      A ≤ normalizer (Y : Set G) → v ∈ Y → d.F ≤ Y := by
  intro N K W A Y hYW hYcard hAY hvY
  let I := d.F ⊓ Y
  have hWcard : Nat.card W = 256 :=
    (card_map_of_injective (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_omega_structure h hN hproper).1
  have hidx : Y.relIndex W = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) Y W bot_le hYW
    rw [relIndex_bot_left, relIndex_bot_left, hYcard, hWcard] at hh
    omega
  have hIidx : I.relIndex d.F ≤ 2 := by
    rw [show I = Y ⊓ d.F from inf_comm _ _, inf_relIndex_right]
    have hh := relIndex_le_of_le_right d.normalizer_core_omega_inclusions.1
      (show Y.relIndex W ≠ 0 by omega)
    exact hh.trans_eq hidx
  have hIlarge : 16 ≤ Nat.card I := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) I d.F bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, d.card] at hh
    nlinarith
  have hAI : A ≤ normalizer (I : Set G) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro x
    exact and_congr (mem_normalizer_iff.mp (map_subtype_le _ ha) x)
      (mem_normalizer_iff.mp (hAY ha) x)
  have hIfix : I ⊓ centralizer (A : Set G) = zpowers v := by
    apply le_antisymm
    · exact hfix ▸ inf_le_inf_right _ (show I ≤ d.F from inf_le_left)
    · apply zpowers_le.mpr
      have hvfix := hfix.symm ▸ mem_zpowers v
      exact ⟨⟨hvfix.1, hvY⟩, hvfix.2⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAcard : Nat.card A = 3 :=
    (card_map_of_injective N.subtype_injective).trans (d.normalizer_three_card h hN hproper Q)
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hm := A.card_modEq_card_inf_centralizer I hA hAI
  rw [hIfix, Nat.card_zpowers, hv] at hm
  change Nat.card I % 3 = 2 % 3 at hm
  have hd : Nat.card I ∈ Nat.divisors 32 := Nat.mem_divisors.mpr
    ⟨d.card ▸ card_dvd_of_le (show I ≤ d.F from inf_le_left), by decide⟩
  rw [show Nat.divisors 32 = {1, 2, 4, 8, 16, 32} by decide] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have hIcard : Nat.card I = 32 := by omega
  have hIF : I = d.F := eq_of_le_of_card_ge inf_le_left (by rw [hIcard, d.card])
  exact hIF ▸ (show I ≤ Y from inf_le_right)

/-- A proper Q-invariant subgroup of omega containing F has no involutions
 outside F, and therefore has omega subgroup F. -/
public theorem second_transfer_invariant_subgroup_omega
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ Y : Subgroup G, Y < W → d.F ≤ Y → A ≤ normalizer (Y : Set G) →
      (omega₁ Y (p := 2)).map Y.subtype = d.F := by
  intro N K X D A W hCD Y hYW hFY hAY
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hWX : W ≤ X := by
    rw [show W = ((omega₁ K (p := 2)).map K.subtype).map N.subtype from
      (map_map _ _ _).symm]
    exact map_mono (map_subtype_le _)
  have hconj (q : Q) (x : G) :
      x ∈ Y ↔ ((q : N) : G) * x * ((q : N) : G)⁻¹ ∈ Y :=
    mem_normalizer_iff.mp (hAY (mem_map_of_mem N.subtype q.property)) x
  have hnotE : ¬ E ≤ Y := by
    intro hEY
    apply hYW.not_ge
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    intro k hk
    have hk2 : (N.subtype.comp K.subtype k) ^ 2 = 1 :=
      congrArg (N.subtype.comp K.subtype) hk
    obtain ⟨q, hq⟩ := d.normalizer_core_involution_transport h hN hproper Q hCD
      (N.subtype.comp K.subtype k) (mem_map_of_mem N.subtype k.property) hk2
    exact (hconj q _).mpr ((sup_le hEY hFY) hq)
  have hsquare (y : G) (hy : y ∈ Y) (hy2 : y ^ 2 = 1) : y ∈ d.F := by
    obtain ⟨q, hq⟩ := d.normalizer_core_involution_transport h hN hproper Q hCD
      y (hWX (hYW.le hy)) hy2
    let t := ((q : N) : G) * y * ((q : N) : G)⁻¹
    have htY : t ∈ Y := (hconj q y).mp hy
    have ht2 : t ^ 2 = 1 := by
      change (MulAut.conj ((q : N) : G) y) ^ 2 = 1
      rw [← map_pow, hy2, map_one]
    have htF : t ∈ d.F := by
      rcases d.elementary_join_involution h t hq ht2 with htE | htF
      · by_contra htF
        let B := E ⊓ d.F
        let : IsElementaryAbelian 2 (commutator J) :=
          (parrott_centralizer_structure z h).2.2.2.2.2.1
        let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
        have htB : t ∉ B := fun hh => htF hh.2
        have htNB : t ∈ normalizer (B : Set G) := by
          apply Subgroup.centralizer_le_normalizer _
          intro a ha
          exact congrArg E.subtype (mul_comm (⟨a, ha.1⟩ : E) ⟨t, htE⟩)
        have hBcard : Nat.card B = 16 := d.inf_card
        have hEcard : Nat.card E = 32 :=
          (card_map_of_injective (f := H.subtype.comp J.subtype)
            (H.subtype_injective.comp J.subtype_injective)).trans
            (parrott_centralizer_structure z h).2.2.2.2.2.2.1
        have hspan : B ⊔ zpowers t = E := by
          apply eq_of_le_of_card_ge (sup_le inf_le_left (zpowers_le.mpr htE))
          rw [card_sup_zpowers_of_normalizing_involution B t ht2 htB htNB, hBcard, hEcard]
        apply hnotE
        rw [← hspan]
        exact sup_le (inf_le_right.trans hFY) (zpowers_le.mpr htY)
      · exact htF
    exact (mem_normalizer_iff.mp (q : N).property y).mpr htF
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    intro y hy
    exact hsquare y y.property (congrArg Y.subtype hy)
  · intro f hf
    refine ⟨⟨f, hFY hf⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    let : IsElementaryAbelian 2 d.F := d.elementary
    exact elemPow_eq_one_of_isElementaryAbelian f hf

/-- The center of an invariant order-128 subgroup containing F is the center
 of omega. Orbit counting rules out the only intermediate order, sixteen. -/
public theorem second_transfer_invariant_subgroup_center
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let i := N.subtype.comp K.subtype
    let W := U.map i
    let ZW := (center U).map (i.comp U.subtype)
    let A := (Q : Subgroup N).map N.subtype
    ∀ Y : Subgroup G, Y ≤ W → Nat.card Y = 128 →
      A ≤ normalizer (Y : Set G) → d.F ≤ Y → (center Y).map Y.subtype = ZW := by
  intro N K U i W ZW A Y hYW hYcard hAY hFY
  let ZY := (center Y).map Y.subtype
  have hZWF : ZW ≤ d.F := d.normalizer_core_omega_inclusions.2.2
  have hZYF : ZY ≤ d.F := by
    rw [← d.centralizer_eq]
    rintro c ⟨cY, hcY, rfl⟩ f hf
    exact congrArg Y.subtype (mem_center_iff.mp hcY ⟨f, hFY hf⟩)
  have hZWZY : ZW ≤ ZY := by
    rintro t ⟨tU, htU, rfl⟩
    have htF : (i.comp U.subtype) tU ∈ d.F := hZWF (mem_map_of_mem _ htU)
    refine ⟨⟨(i.comp U.subtype) tU, hFY htF⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    obtain ⟨k, hk, he⟩ := hYW y.property
    have hh := congrArg (i.comp U.subtype) (mem_center_iff.mp htU ⟨k, hk⟩)
    change i k * (i.comp U.subtype) tU = (i.comp U.subtype) tU * i k at hh
    rwa [he] at hh
  have hZWcard : Nat.card ZW = 8 :=
    (card_map_of_injective (f := i.comp U.subtype)
      ((N.subtype_injective.comp K.subtype_injective).comp U.subtype_injective)).trans
      (d.normalizer_core_omega_structure h hN hproper).2.1
  have hZYlarge : 8 ≤ Nat.card ZY := hZWcard ▸ card_le_of_le hZWZY
  have hZYnot : Nat.card ZY ≠ 32 := by
    intro hc
    have heq : ZY = d.F := eq_of_le_of_card_ge hZYF (by rw [hc, d.card])
    have hYF : Y ≤ d.F := by
      rw [← d.centralizer_eq]
      intro y hy f hf
      rw [← heq] at hf
      obtain ⟨fY, hfY, rfl⟩ := hf
      exact (congrArg Y.subtype (mem_center_iff.mp hfY ⟨y, hy⟩)).symm
    have hh := card_le_of_le hYF
    rw [hYcard, d.card] at hh
    omega
  have hZYfix : ZY ⊓ centralizer (A : Set G) = zpowers v := by
    apply le_antisymm
    · exact hfix ▸ inf_le_inf_right _ hZYF
    · apply zpowers_le.mpr
      exact ⟨hZWZY (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).1,
        (hfix.symm ▸ mem_zpowers v).2⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAcard : Nat.card A = 3 :=
    (card_map_of_injective N.subtype_injective).trans (d.normalizer_three_card h hN hproper Q)
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hAZY : A ≤ normalizer (ZY : Set G) :=
    hAY.trans (normalizer_le_normalizer_characteristic_image Y (center Y))
  have hm := A.card_modEq_card_inf_centralizer ZY hA hAZY
  rw [hZYfix, Nat.card_zpowers, hv] at hm
  change Nat.card ZY % 3 = 2 % 3 at hm
  have hd : Nat.card ZY ∈ Nat.divisors 32 := Nat.mem_divisors.mpr
    ⟨d.card ▸ card_dvd_of_le hZYF, by decide⟩
  rw [show Nat.divisors 32 = {1, 2, 4, 8, 16, 32} by decide] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have hZYcard : Nat.card ZY = 8 := by omega
  exact (eq_of_le_of_card_ge hZWZY (by rw [hZWcard, hZYcard])).symm

/-- The invariant subgroup produced by the second transfer has omega F and
 the same center as the normalizer-core omega, retaining the supplied root. -/
public theorem second_transfer_invariant_subgroup_geometry
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let U := omega₁ K (p := 2)
    let W := U.map (N.subtype.comp K.subtype)
    let ZW := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    ∀ b ∈ X, orderOf b = 4 → b ^ 2 = v →
      X ⊓ centralizer (A : Set G) = zpowers b →
      ∀ Y : Subgroup G, Y ≤ W → Nat.card Y = 128 →
        A ≤ normalizer (Y : Set G) → b ∉ Y →
        (omega₁ Y (p := 2)).map Y.subtype = d.F ∧
        (center Y).map Y.subtype = ZW := by
  intro N K X D A hCD v hv hfix U W ZW b hbX _hb4 hb2 _hbgen Y hYW hYcard hAY hbY
  have hbW : b ∈ W := d.normalizer_fixed_root_mem_omega h hN hproper Q v hv hfix b hbX hb2
  have hWcard : Nat.card W = 256 :=
    (card_map_of_injective (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_omega_structure h hN hproper).1
  have hidx : Y.relIndex W = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) Y W bot_le hYW
    rw [relIndex_bot_left, relIndex_bot_left, hYcard, hWcard] at hh
    omega
  have hvY : v ∈ Y := by
    have hh := sq_mem_of_index_two (H := Y.subgroupOf W) hidx (⟨b, hbW⟩ : W)
    change b ^ 2 ∈ Y at hh
    rwa [hb2] at hh
  have hFY := d.second_transfer_invariant_subgroup_contains_elementary
    h hN hproper Q v hv hfix Y hYW hYcard hAY hvY
  have hlt : Y < W := lt_of_le_of_ne hYW (fun he => hbY (he.symm ▸ hbW))
  exact ⟨d.second_transfer_invariant_subgroup_omega h hN hproper Q hCD Y hlt hFY hAY,
    d.second_transfer_invariant_subgroup_center h hN hproper Q v hv hfix Y hYW hYcard hAY hFY⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
