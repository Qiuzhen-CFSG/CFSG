module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterLocalBounds
public import Stellmacher.Recognition.Parrott.CoreQuotientAction
public import Theory.GroupAction.FiveFourInvolutionFixed
public import Theory.GroupAction.InvolutionDisplacementSubgroup
public import Theory.GroupTheory.Commutator.IndexTwo
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The large derived intersection of the chosen center

Write `B = K ∩ S` and `U = E ∩ Z(S)` in the notation of the chosen
centralizer. If `|U| = 8`, the local bounds give `|B| = 64`. The central
commutator pairing gives `|C_K(U)| = 128`; the normalized product `EB`
has the same order and hence equals this centralizer. The three-subgroups
lemma then puts `[S,K]` in `EB`: both `[U,S]` and `[[K,U],S]` vanish.
This supplies the ambient subgroup form of the pairing transport, without
choosing a bilinear model or assuming an outer lift is an involution.

In the elementary quotient `J/J′` of order sixteen, the image of `EB`
has order four and contains every displacement of an element of `S`
outside the core. Such an element acts as an involution with four fixed
points, by the faithful five-four action. Rank-nullity and binary
quadraticity therefore force it to fix the image of `EB` pointwise.
Thus `[S,B] ≤ E`; since `B` has index two in `S`, this gives `[S,S] ≤ E`.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and p.676, the nonabelian image of the chosen centralizer.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
/-- The chosen centralizer meets the derived core in its fixed-join hyperplane. -/
public theorem chosen_derived_intersection (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    E ⊓ S = E ⊓ d.F ∧ Nat.card (E ⊓ S : Subgroup G) = 16 := by
  intro H E S
  have hEH : E ≤ H := by
    rintro x ⟨b, _, rfl⟩
    exact b.val.property
  have heq : E ⊓ S = E ⊓ d.F := by
    change E ⊓ (H ⊓ centralizer ({(d.a : G)} : Set G)) = _
    rw [← inf_assoc, inf_eq_left.mpr hEH, d.inf_eq]
  exact ⟨heq, heq ▸ d.inf_card⟩

/-- In the large-center branch the annihilator inside the core is exactly `EB`. -/
public theorem chosen_large_center_core_centralizer (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    Nat.card (E ⊓ Z : Subgroup G) = 8 →
      K ⊓ centralizer ((E ⊓ Z : Subgroup G) : Set G) = E ⊔ (K ⊓ S) ∧
      Nat.card (E ⊔ (K ⊓ S) : Subgroup G) = 128 := by
  intro H J K E S Z hUcard
  let B := K ⊓ S
  let U := E ⊓ Z
  let C := centralizer (U : Set G)
  have hEK : E ≤ K := by
    rintro x ⟨b, _, rfl⟩
    exact mem_map_of_mem H.subtype b.property
  have hSC : S ≤ C := by
    intro s hs u hu
    obtain ⟨uS, huS, rfl⟩ := hu.2
    exact (congrArg S.subtype (mem_center_iff.mp huS ⟨s, hs⟩)).symm
  have hEC : E ≤ C := by
    obtain ⟨_, _, _, _, _, hElem, _, _⟩ := parrott_centralizer_structure z h
    let : IsElementaryAbelian 2 (commutator J) := hElem
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show U ≤ E from inf_le_left))
  have hEBS : E ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro e he b hb
    exact ⟨K.mul_mem (K.mul_mem (hEK he) hb.1) (K.inv_mem (hEK he)),
      (d.derived_le_chosen_centralizer_normalizer h he b).mp hb.2⟩
  have hBcard : Nat.card B = 64 := by
    exact (d.chosen_card_of_core_relIndex_two h
      (d.chosen_core_relIndex_eq_two_of_center_derived_card_ge_eight h hUcard.ge)).1
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans
      (parrott_centralizer_structure z h).2.2.2.2.2.2.1
  have hBE : B ⊓ E = E ⊓ S := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hEK hx.1, hx.2⟩, hx.1⟩⟩
  have hsupCard : Nat.card (E ⊔ B : Subgroup G) = 128 := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes B E hEBS
    rw [hBcard, hEcard, hBE, d.chosen_derived_intersection.2, sup_comm] at hc
    omega
  have hCcard : Nat.card (K ⊓ C : Subgroup G) = 128 := by
    have hzU : zpowers z ≤ U := zpowers_le.mpr
      ⟨d.z_mem_inf.1, d.chosen_centralizer_center.1⟩
    have hc := parrott_core_subgroup_centralizer_card z h U hzU inf_le_left
    have hmap := card_map_of_injective (K := C.subgroupOf K) K.subtype_injective
    rw [subgroupOf_map_subtype, inf_comm] at hmap
    change Nat.card U * Nat.card (C.subgroupOf K) = 1024 at hc
    rw [← hmap] at hc
    change Nat.card U = 8 at hUcard
    rw [hUcard] at hc
    omega
  have hle : E ⊔ B ≤ K ⊓ C :=
    sup_le (le_inf hEK hEC) (le_inf inf_le_left (inf_le_right.trans hSC))
  exact ⟨(eq_of_le_of_card_ge hle (by rw [hCcard, hsupCard])).symm, hsupCard⟩

/-- Equivariance of the central pairing, expressed using ambient commutators. -/
public theorem chosen_large_center_mixed_commutator (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    Nat.card (E ⊓ Z : Subgroup G) = 8 → ⁅S, K⁆ ≤ E ⊔ (K ⊓ S) := by
  intro H J K E S Z hUcard
  let U := E ⊓ Z
  have hSU : S ≤ centralizer (U : Set G) := by
    intro s hs u hu
    obtain ⟨uS, huS, rfl⟩ := hu.2
    exact (congrArg S.subtype (mem_center_iff.mp huS ⟨s, hs⟩)).symm
  have hKU : ⁅K, U⁆ ≤ zpowers z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro u hu k hk
    obtain ⟨b, hb, rfl⟩ := hu.1
    obtain ⟨kH, hkJ, rfl⟩ := hk
    obtain ⟨hZ, _, _, _, hupper, _, _, _⟩ := parrott_centralizer_structure z h
    have hbc : ⁅b, (⟨kH, hkJ⟩ : J)⁆ ∈ center J := by
      have hbU : b ∈ Subgroup.upperCentralSeries J 2 := hupper ▸ hb
      simpa only [Subgroup.upperCentralSeries_one] using
        (Subgroup.mem_upperCentralSeries_succ_iff.mp hbU (⟨kH, hkJ⟩ : J))
    rw [← hZ]
    exact mem_map_of_mem (H.subtype.comp J.subtype) hbc
  have hzS : zpowers z ≤ centralizer (S : Set G) := by
    apply zpowers_le.mpr
    intro s hs
    exact mem_centralizer_singleton_iff.mp hs.1
  have hdouble : ⁅⁅S, K⁆, U⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · exact commutator_eq_bot_iff_le_centralizer.mpr (hKU.trans hzS)
    · rw [commutator_comm U S, commutator_eq_bot_iff_le_centralizer.mpr hSU,
        commutator_bot_left]
  have hHK : H ≤ normalizer (K : Set G) := by
    have hm := le_normalizer_map (H := J) H.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] at hm
    exact hm
  have hSK : ⁅S, K⁆ ≤ K :=
    le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hHK)
  rw [← (d.chosen_large_center_core_centralizer h hUcard).1]
  exact le_inf hSK (commutator_eq_bot_iff_le_centralizer.mp hdouble)

/-- If the derived part of the center has order eight, the chosen centralizer
has abelian image modulo the derived core. -/
public theorem chosen_large_center_commutator_le (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let _K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    Nat.card (E ⊓ Z : Subgroup G) = 8 → (commutator S).map S.subtype ≤ E := by
  intro H J K E S Z hUcard
  let D := commutator J
  let B := K ⊓ S
  let embed : J →* G := H.subtype.comp J.subtype
  let V := J ⧸ D
  let q := QuotientGroup.mk' D
  let R := S.subgroupOf H
  let C := (E ⊔ B).comap embed
  let A := C.map q
  have hinj : Function.Injective embed := H.subtype_injective.comp J.subtype_injective
  have hEK : E ≤ K := by
    rintro x ⟨b, _, rfl⟩
    exact mem_map_of_mem H.subtype b.property
  have hcorecomm : ⁅K, K⁆ = E := by
    dsimp only [E]
    rw [← map_map, map_subtype_commutator, map_commutator]
  have hindex : K.relIndex S = 2 :=
    d.chosen_core_relIndex_eq_two_of_center_derived_card_ge_eight h hUcard.ge
  have hRindex : J.relIndex R = 2 := by
    rw [← relIndex_map_map_of_injective J R H.subtype_injective,
      map_subgroupOf_eq_of_le (show S ≤ H from inf_le_left)]
    exact hindex
  have hCmap : C.map embed = E ⊔ B := by
    apply map_comap_eq_self
    have hrange : embed.range = K := by
      rw [MonoidHom.range_comp, J.range_subtype]
    rw [hrange]
    exact sup_le hEK inf_le_left
  have hCcard : Nat.card C = 128 := by
    rw [← card_map_of_injective (K := C) hinj, hCmap]
    exact (d.chosen_large_center_core_centralizer h hUcard).2
  have hDC : D ≤ C := by
    intro j hj
    exact mem_sup_left (mem_map_of_mem embed hj)
  have hDcard : Nat.card D = 32 :=
    (parrott_centralizer_structure z h).2.2.2.2.2.2.1
  have hAcard : Nat.card A = 4 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup J) D C bot_le hDC
    rw [relIndex_bot_left, relIndex_bot_left, hDcard, hCcard] at hc
    have hidx := relIndex_ker C q
    rw [QuotientGroup.ker_mk'] at hidx
    change D.relIndex C = Nat.card A at hidx
    omega
  obtain ⟨helem, hVcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 V := helem
  obtain ⟨f, hf, hformula⟩ := parrott_core_quotient_action z h
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let modelAction := f.comp e.symm.toMonoidHom
  have hmodelInj : Function.Injective modelAction := hf.comp e.symm.injective
  have hmixed : ⁅K, S⁆ ≤ E ⊔ B := by
    rw [commutator_comm]
    exact d.chosen_large_center_mixed_commutator h hUcard
  have hfix (y : H) (hyS : (y : G) ∈ S) (hyJ : y ∉ J) :
      A ≤ FixedPoints.subgroup (zpowers (f (QuotientGroup.mk' J y))) V := by
    let b := f (QuotientGroup.mk' J y)
    have hy2 : y ^ 2 ∈ J := by
      have hh := (J.subgroupOf R).mul_self_mem_of_index_two hRindex
        (⟨y, hyS⟩ : R)
      simpa only [mem_subgroupOf, coe_mul, pow_two] using hh
    have hq2 : orderOf (QuotientGroup.mk' J y) = 2 := by
      apply orderOf_eq_prime
      · rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr hy2
      · exact fun heq => hyJ ((QuotientGroup.eq_one_iff _).mp heq)
    have hb2 : b ^ 2 = 1 := by
      change (f (QuotientGroup.mk' J y)) ^ 2 = 1
      have hqSquare : QuotientGroup.mk' J (y ^ 2) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hy2
      rw [← map_pow, ← map_pow, hqSquare, map_one]
    have hfixed : Nat.card (FixedPoints.subgroup (zpowers b) V) = 4 := by
      have hh := Theory.GroupAction.five_four_involution_fixed_displacement
        hVcard φ hφ modelAction hmodelInj (e (QuotientGroup.mk' J y))
        (by rw [e.orderOf_eq]; exact hq2)
      have heval : modelAction (e (QuotientGroup.mk' J y)) = b :=
        congrArg f (e.symm_apply_apply _)
      rw [heval] at hh
      exact hh.1
    apply MulAut.subgroup_le_fixed_of_displacement_le b hb2 A
      (by rw [hVcard, hAcard, hfixed])
    intro v
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective D v
    let j' : J := ⟨y * (j : H) * y⁻¹,
      (inferInstance : J.Normal).conj_mem j j.property y⟩
    have hformula' : b (q j) = q j' := hformula y j j' rfl
    change (q j)⁻¹ * b (q j) ∈ A
    rw [hformula', ← map_inv, ← map_mul]
    apply mem_map_of_mem q
    change embed (j⁻¹ * j') ∈ E ⊔ B
    have hm := hmixed (commutator_mem_commutator
      (K.inv_mem (mem_map_of_mem H.subtype j.property)) hyS)
    change (embed j)⁻¹ * ((y : G) * embed j * (y : G)⁻¹) ∈ E ⊔ B
    simpa only [embed, MonoidHom.comp_apply, subtype_apply, commutatorElement_def, inv_inv, mul_assoc] using hm
  rw [map_subtype_commutator,
    commutator_eq_of_relIndex_two B S inf_le_right (by
      dsimp only [B]
      rw [inf_relIndex_right]
      exact hindex), commutator_comm B S]
  apply commutator_le.mpr
  intro s hs b hb
  by_cases hsK : s ∈ K
  · rw [← hcorecomm]
    exact commutator_mem_commutator hsK hb.1
  let y : H := ⟨s, hs.1⟩
  have hyJ : y ∉ J := fun hy => hsK (mem_map_of_mem H.subtype hy)
  obtain ⟨bH, hbJ, rfl⟩ := hb.1
  let j : J := ⟨bH, hbJ⟩
  let j' : J := ⟨y * (j : H) * y⁻¹,
    (inferInstance : J.Normal).conj_mem j j.property y⟩
  have hjA : q j ∈ A := mem_map_of_mem q (show j ∈ C from mem_sup_right hb)
  have hqfix := hfix y hs hyJ hjA
    ⟨f (QuotientGroup.mk' J y), mem_zpowers _⟩
  have hqeq : q j' = q j := (hformula y j j' rfl).symm.trans hqfix
  have hmem : j' / j ∈ D := QuotientGroup.eq_iff_div_mem.mp hqeq
  have hm := mem_map_of_mem embed hmem
  change (s * (bH : G) * s⁻¹) / (bH : G) ∈ E at hm
  simpa only [commutatorElement_def, div_eq_mul_inv, subtype_apply] using hm

end Stellmacher.Recognition.ParrottSecondElementaryData
