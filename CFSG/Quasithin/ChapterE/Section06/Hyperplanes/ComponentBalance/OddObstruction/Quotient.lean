module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.CentralTwoQuotientOddCore

/-!
# The quotient in the odd-core obstruction argument

For H = C_G(A), the kernel is O(H) joined with the actual subgroup of H
induced by A. The latter is central in H. For A ≤ U ≤ V with V elementary
abelian, coprimality gives U ∩ (O(H)A) = A, so the image of U has order
[U : A]. Odd-kernel normalizer lifting proves that the image of
O(C_G(U)) is normal in the quotient centralizer. Its image cannot vanish
unless the original odd core lies in O(H). Finally, E.6.5 transports the
actual Sylow subgroup Q = C_T(V), retaining V ≤ Z(Q).

These results supply the quotient setup in E.6.19. Component extraction,
lifting, and model inspection remain separate obligations. No ambient
normality of A or O(H) is asserted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19,
printed p.252 (PDF p.263).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction

variable {G : Type*} [Group G]

/-- The central subgroup A ∩ C_G(A), considered inside C_G(A). -/
theorem subspace_le_center (A : Subgroup G) :
    A.subgroupOf (centralizer (A : Set G)) ≤ center (centralizer (A : Set G)) := by
  intro a ha
  rw [mem_center_iff]
  intro x
  exact Subtype.ext (x.property a ha).symm

instance subspace_normal (A : Subgroup G) :
    (A.subgroupOf (centralizer (A : Set G))).Normal := by
  constructor
  intro a ha x
  have hc := mem_center_iff.mp (subspace_le_center A ha) x
  simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using ha

/-- The source kernel O(C_G(A)) A, with both factors inside C_G(A). -/
def quotientKernel (A : Subgroup G) : Subgroup (centralizer (A : Set G)) :=
  pPrimeCore 2 (centralizer (A : Set G)) ⊔ A.subgroupOf (centralizer (A : Set G))

instance quotientKernel_normal (A : Subgroup G) : (quotientKernel A).Normal :=
  inferInstanceAs ((_ ⊔ A.subgroupOf (centralizer (A : Set G))) :
    Subgroup (centralizer (A : Set G))).Normal

/-- The actual group C_G(A)/(O(C_G(A)) A). -/
abbrev CentralizerQuotient (A : Subgroup G) :=
  centralizer (A : Set G) ⧸ quotientKernel A

/-- The actual quotient homomorphism. -/
def quotientMap (A : Subgroup G) : centralizer (A : Set G) →* CentralizerQuotient A :=
  QuotientGroup.mk' (quotientKernel A)

/-- The image of a subgroup under the actual quotient map. -/
def quotientImage (A U : Subgroup G) : Subgroup (CentralizerQuotient A) :=
  (U.subgroupOf (centralizer (A : Set G))).map (quotientMap A)

theorem quotientMap_ker (A : Subgroup G) : (quotientMap A).ker = quotientKernel A :=
  QuotientGroup.ker_mk' _

theorem quotientMap_surjective (A : Subgroup G) : Function.Surjective (quotientMap A) :=
  QuotientGroup.mk'_surjective _

variable [Finite G] {A U V : Subgroup G}

omit [Finite G] in
/-- A subspace's centralizer contains every larger subspace of V. -/
theorem subspace_le_centralizer [IsElementaryAbelian 2 V]
    (hAV : A ≤ V) (hUV : U ≤ V) : U ≤ centralizer (A : Set G) :=
  hUV.trans (V.le_centralizer.trans (Subgroup.centralizer_le hAV))

/-- The quotient kernel meets U in precisely A. -/
theorem kernel_inf_subspace [IsElementaryAbelian 2 V]
    (hAU : A ≤ U) (hUV : U ≤ V) :
    quotientKernel A ⊓ U.subgroupOf (centralizer (A : Set G)) =
      A.subgroupOf (centralizer (A : Set G)) := by
  let H := centralizer (A : Set G)
  let U' := U.subgroupOf H
  let A' := A.subgroupOf H
  have hUp : IsPGroup 2 U' :=
    ((IsElementaryAbelian.isPGroup 2 V).to_le hUV).comap_subtype
  obtain ⟨n, hn⟩ := hUp.exists_card_eq
  have hd : Disjoint (pPrimeCore 2 H) U' :=
    disjoint_of_coprime_natCard (by
      rw [hn]
      exact (pPrimeCore_coprime_card (p := 2) (G := H)).symm.pow_right n)
  apply le_antisymm
  · rintro x ⟨hx, hxU⟩
    obtain ⟨o, ho, a, ha, rfl⟩ := mem_sup_of_normal_left.mp hx
    have hoU : o ∈ U' := by
      have haU : a ∈ U' := hAU ha
      simpa only [mul_inv_cancel_right] using U'.mul_mem hxU (U'.inv_mem haU)
    have ho1 : o = 1 := Subgroup.disjoint_def.mp hd ho hoU
    simpa only [ho1, one_mul] using ha
  · exact le_inf le_sup_right (fun _ ha => hAU ha)

/-- The cardinality of the actual image is the relative subspace index. -/
theorem card_quotientImage [IsElementaryAbelian 2 V]
    (hAU : A ≤ U) (hUV : U ≤ V) : Nat.card (quotientImage A U) = A.relIndex U := by
  let H := centralizer (A : Set G)
  have hUH : U ≤ H := subspace_le_centralizer (hAU.trans hUV) hUV
  rw [quotientImage, ← relIndex_ker, quotientMap_ker, ← relIndex_subgroupOf hUH]
  unfold relIndex
  have he : (quotientKernel A).subgroupOf (U.subgroupOf H) =
      (A.subgroupOf H).subgroupOf (U.subgroupOf H) := by
    ext x
    exact ⟨fun hx => (show (x : H) ∈ A.subgroupOf H from
      kernel_inf_subspace hAU hUV ▸ ⟨hx, x.property⟩),
      fun hx => (show A.subgroupOf H ≤ quotientKernel A from le_sup_right) hx⟩
  rw [he]

/-- In E.6.19 the image of U is a subgroup of order two. -/
theorem card_quotientImage_eq_two [IsElementaryAbelian 2 V]
    (hAU : A ≤ U) (hUV : U ≤ V) (hindex : A.relIndex U = 2) :
    Nat.card (quotientImage A U) = 2 :=
  (card_quotientImage hAU hUV).trans hindex

omit [Finite G] in
private theorem sup_kernel_eq_sup_core {X : Subgroup (centralizer (A : Set G))}
    (hAX : A.subgroupOf (centralizer (A : Set G)) ≤ X) :
    X ⊔ quotientKernel A = X ⊔ pPrimeCore 2 (centralizer (A : Set G)) := by
  unfold quotientKernel
  rw [← sup_assoc, sup_eq_left.mpr (hAX.trans le_sup_left)]

/-- Normalizers of subspaces containing A lift through the actual quotient.
The odd-kernel normalizer theorem applies because adjoining the kernel to U
is the same as adjoining just O(C_G(A)). -/
theorem normalizer_quotientImage [IsElementaryAbelian 2 V]
    (hAU : A ≤ U) (hUV : U ≤ V) :
    normalizer (quotientImage A U : Set (CentralizerQuotient A)) =
      (normalizer (U.subgroupOf (centralizer (A : Set G)) :
        Set (centralizer (A : Set G)))).map (quotientMap A) := by
  let H := centralizer (A : Set G)
  let U' := U.subgroupOf H
  let O := pPrimeCore 2 H
  let q₀ := QuotientGroup.mk' O
  let _ : Fact (IsPGroup 2 U') :=
    ⟨((IsElementaryAbelian.isPGroup 2 V).to_le hUV).comap_subtype⟩
  have hn := normalizer_map_quotient_eq_map_normalizer 2 U' O
    inferInstance (pPrimeCore_coprime_card (p := 2) (G := H))
  have hn' := congrArg (Subgroup.comap q₀) hn
  rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective O),
    comap_map_eq, comap_map_eq, QuotientGroup.ker_mk'] at hn'
  apply Subgroup.comap_injective (quotientMap_surjective A)
  change (normalizer (U'.map (quotientMap A) : Set (CentralizerQuotient A))).comap
    (quotientMap A) = _
  rw [comap_normalizer_eq_of_surjective _ (quotientMap_surjective A),
    comap_map_eq, comap_map_eq, quotientMap_ker]
  rw [sup_kernel_eq_sup_core (fun _ ha => hAU ha),
    sup_kernel_eq_sup_core ((show A.subgroupOf H ≤ U' from fun _ ha => hAU ha).trans
      Subgroup.le_normalizer)]
  exact hn'

/-- The quotient has trivial odd core: first factor out O(H), then the
central two-subgroup which is the image of A. -/
theorem quotient_oddCore_eq_bot [IsElementaryAbelian 2 V] (hAV : A ≤ V) :
    pPrimeCore 2 (CentralizerQuotient A) = ⊥ := by
  let H := centralizer (A : Set G)
  let O := pPrimeCore 2 H
  let q₀ := QuotientGroup.mk' O
  let N := (quotientKernel A).map q₀
  have hN : N = (A.subgroupOf H).map q₀ := by
    simp only [N, quotientKernel, Subgroup.map_sup, O, q₀, H, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hNp : IsPGroup 2 N := by
    rw [hN]
    exact (((IsElementaryAbelian.isPGroup 2 V).to_le hAV).comap_subtype).map q₀
  have hNc : N ≤ center (H ⧸ O) := by
    rw [hN]
    rintro x ⟨a, ha, rfl⟩
    rw [mem_center_iff]
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective O y
    simpa only [q₀, map_mul] using congrArg q₀
      (mem_center_iff.mp (subspace_le_center A ha) b)
  have hz := pPrimeCore_quotient_eq_bot_of_central_two_subgroup N hNc hNp
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  let e := QuotientGroup.quotientQuotientEquivQuotient O (quotientKernel A) le_sup_left
  rw [← pPrimeCore_map_iso 2 e, hz, Subgroup.map_bot]

private theorem oddCentralizer_coprime (U : Subgroup G) :
    Nat.Coprime 2 (Nat.card (oddCentralizer U)) :=
  (pPrimeCore_coprime_card (p := 2) (G := centralizer (U : Set G))).of_dvd_right
    (Subgroup.card_map_dvd _ _)

private theorem odd_subgroup_le_core_of_le_kernel [IsElementaryAbelian 2 V]
    (hAV : A ≤ V) (R : Subgroup (centralizer (A : Set G)))
    (hR : Nat.Coprime 2 (Nat.card R)) (hRN : R ≤ quotientKernel A) :
    R ≤ pPrimeCore 2 (centralizer (A : Set G)) := by
  let H := centralizer (A : Set G)
  let O := pPrimeCore 2 H
  let q₀ := QuotientGroup.mk' O
  have hmap : R.map q₀ ≤ (A.subgroupOf H).map q₀ := by
    have hh := map_mono (f := q₀) hRN
    simpa only [quotientKernel, Subgroup.map_sup, O, q₀, H, QuotientGroup.map_mk'_self,
      bot_sup_eq] using hh
  have hAp : IsPGroup 2 ((A.subgroupOf H).map q₀) :=
    (((IsElementaryAbelian.isPGroup 2 V).to_le hAV).comap_subtype).map q₀
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hd : Disjoint (R.map q₀) ((A.subgroupOf H).map q₀) :=
    disjoint_of_coprime_natCard (by
      rw [hn]
      exact (hR.of_dvd_right (card_map_dvd R q₀)).symm.pow_right n)
  have hb : R.map q₀ = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact Subgroup.disjoint_def.mp hd hx (hmap hx)
  simpa only [q₀, QuotientGroup.ker_mk'] using (map_eq_bot_iff R).mp hb

/-- Failure of odd-core containment survives in the quotient centralizer.
Only the elementary subspace conditions are used here; the component extraction
is a separate obligation. -/
theorem quotient_centralizer_oddCore_ne_bot [IsElementaryAbelian 2 V]
    (hAU : A ≤ U) (hUV : U ≤ V)
    (hfail : ¬ oddCentralizer U ≤ oddCentralizer A) :
    pPrimeCore 2 (centralizer (quotientImage A U : Set (CentralizerQuotient A))) ≠ ⊥ := by
  let H := centralizer (A : Set G)
  let R := oddCentralizer U
  let R' := R.subgroupOf H
  let S := R'.map (quotientMap A)
  let C := centralizer (quotientImage A U : Set (CentralizerQuotient A))
  have hUH : U ≤ H := subspace_le_centralizer (hAU.trans hUV) hUV
  have hRH : R ≤ H := (oddCentralizer_le U).trans (Subgroup.centralizer_le hAU)
  have hRc : Nat.Coprime 2 (Nat.card R') := (oddCentralizer_coprime U).of_dvd_right
    (card_comap_dvd_of_injective R H.subtype H.subtype_injective)
  have hSC : S ≤ C := by
    rintro x ⟨r, hr, rfl⟩ u ⟨u, hu, rfl⟩
    exact (map_mul (quotientMap A) u r).symm.trans
      ((congrArg (quotientMap A) (Subtype.ext (oddCentralizer_le U hr u hu))).trans
        (map_mul (quotientMap A) r u))
  have hnorm : normalizer (U.subgroupOf H : Set H) ≤ normalizer (R' : Set H) := by
    rw [← subgroupOf_normalizer_eq hUH, ← subgroupOf_normalizer_eq hRH]
    exact comap_mono ((normalizer_le_normalizer_centralizer U).trans
      (normalizer_le_normalizer_characteristic_image (centralizer (U : Set G))
        (pPrimeCore 2 (centralizer (U : Set G)))))
  have hCN : C ≤ normalizer (S : Set (CentralizerQuotient A)) := by
    apply (centralizer_le_normalizer _).trans
    rw [normalizer_quotientImage hAU hUV]
    exact (map_mono hnorm).trans (le_normalizer_map (quotientMap A))
  have hSn : (S.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hSC).mpr hCN
  have hSc : Nat.Coprime 2 (Nat.card (S.subgroupOf C)) :=
    (hRc.of_dvd_right (card_map_dvd R' (quotientMap A))).of_dvd_right
      (card_comap_dvd_of_injective S C.subtype C.subtype_injective)
  have hcore : S.subgroupOf C ≤ pPrimeCore 2 C := le_sSup ⟨hSn, hSc⟩
  intro hz
  have hb : S = ⊥ := by
    have hb' : S.subgroupOf C = ⊥ := le_bot_iff.mp (hz ▸ hcore)
    have hm := congrArg (Subgroup.map C.subtype) hb'
    simpa only [map_subgroupOf_eq_of_le hSC, Subgroup.map_bot] using hm
  have hRN : R' ≤ quotientKernel A := by
    rw [← quotientMap_ker]
    exact (map_eq_bot_iff R').mp hb
  have hRO := odd_subgroup_le_core_of_le_kernel (hAU.trans hUV) R' hRc hRN
  apply hfail
  intro x hx
  exact ⟨⟨x, hRH hx⟩, hRO hx, rfl⟩

/-- E.6.5 gives the actual Sylow subgroup of C_G(A), and V centralizes it.
The equality specifies its ambient image, rather than replacing Sylow status
by a two-subgroup hypothesis. -/
theorem sylow_geometry {K : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : HypothesisE61 K T M V) (hA : A ∈ obstructionFamily M V) :
    ∃ S : Sylow 2 (centralizer (A : Set G)),
      (S : Subgroup (centralizer (A : Set G))).map (centralizer (A : Set G)).subtype =
        sylowCentralizer (T : Subgroup G) V ∧
      V.subgroupOf (centralizer (A : Set G)) ≤ (S : Subgroup (centralizer (A : Set G))) ∧
      V.subgroupOf (centralizer (A : Set G)) ≤ centralizer (S : Set (centralizer (A : Set G))) := by
  let _ := h.elementary
  obtain ⟨S, hS⟩ := h.sylow_obstruction hA
  refine ⟨S, hS, ?_, ?_⟩
  · intro v hv
    have hvQ : (v : G) ∈ sylowCentralizer (T : Subgroup G) V :=
      ⟨h.le_sylow hv, V.le_centralizer hv⟩
    rw [← hS] at hvQ
    obtain ⟨s, hs, he⟩ := hvQ
    exact (Subtype.ext he : s = v) ▸ hs
  · intro v hv s hs
    have hsQ : (s : G) ∈ sylowCentralizer (T : Subgroup G) V :=
      hS ▸ mem_map_of_mem _ hs
    exact Subtype.ext (hsQ.2 v hv).symm

/-- The same quotient map carries Q to a Sylow subgroup and V into its center. -/
theorem quotient_sylow_geometry {K : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : HypothesisE61 K T M V) (hA : A ∈ obstructionFamily M V) :
    ∃ S : Sylow 2 (CentralizerQuotient A),
      (S : Subgroup (CentralizerQuotient A)) =
        quotientImage A (sylowCentralizer (T : Subgroup G) V) ∧
      quotientImage A V ≤ (S : Subgroup (CentralizerQuotient A)) ∧
      quotientImage A V ≤ centralizer (S : Set (CentralizerQuotient A)) := by
  let H := centralizer (A : Set G)
  obtain ⟨S, hS, hVS, hVc⟩ := sylow_geometry h hA
  let Sbar := S.mapSurjective (f := quotientMap A) (quotientMap_surjective A)
  have hQH : sylowCentralizer (T : Subgroup G) V ≤ H :=
    inf_le_right.trans (Subgroup.centralizer_le hA.1)
  have hSeq : (S : Subgroup H) = (sylowCentralizer (T : Subgroup G) V).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hQH]
  refine ⟨Sbar, ?_, map_mono hVS, ?_⟩
  · change (S : Subgroup H).map (quotientMap A) = _
    rw [hSeq]
    rfl
  · rintro v ⟨v, hv, rfl⟩ s ⟨s, hs, rfl⟩
    simpa only [map_mul] using congrArg (quotientMap A) (hVc hv s hs)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
