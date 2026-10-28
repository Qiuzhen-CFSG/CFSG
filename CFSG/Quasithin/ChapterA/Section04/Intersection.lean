module

public import CFSG.Quasithin.ChapterA.Section04.Defs
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Subnormal
public import CFSG.Quasithin.ChapterG.Section08.ThetaFaithfulness
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Intersection core recovery and equality of maximal two-locals

This proves all three conclusions of Aschbacher–Smith A.4.4, printed p.58
(PDF p.69), in the combined manuscript of 1 March 2004.

The alternatives are actual membership in Θ(H/O₂(H)), or subnormality in
F*(H/O₂(H)) together with the prime-order centralizer condition. The latter
is also stated elementwise below. G.8.9 supplies layer absorption; the layer
is perfect and the Fitting subgroup has odd order, so X* is two-perfect.
Subnormality makes its two-core trivial. A.4.2(3) therefore centralizes the
image of O₂(H ∩ K), and G.8.9 kills that image.

For maximal two-locals, every nontrivial characteristic subgroup of the
core has the same full normalizer. This proves the relative C(K,Q) bound.
The equality clause applies core recovery in the opposite direction using
the literal preimage of F*(K/O₂(K)), then identifies the common normalizer.
The relative characteristic-normalizer formula extends the existing C.1.5
construction without importing Chapter C or the parent A.4 module.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section08
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

private theorem odd_twoPerfect {A : Type*} [Group A] [Finite A]
    (hodd : Odd (Nat.card A)) : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have ho : Odd (Nat.card (A ⧸ N)) := hodd.of_dvd_nat N.index_dvd_card
  have hc : Nat.card (A ⧸ N) = 1 := hp.card_eq_or_dvd.resolve_right ho.not_two_dvd_nat
  exact N.index_eq_one.mp hc

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (A ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

private theorem twoPerfect_of_layer_le (hc : pCore 2 G = ⊥)
    (X : Subgroup G) (hXF : X ≤ generalizedFitting G)
    (hEX : componentLayer G ≤ X) : IsPPerfect 2 X := by
  let E := componentLayer G
  have hp : Group.IsPerfect E := by
    rw [isPerfect_iff]
    apply le_antisymm E.commutator_le_self
    apply sSup_le
    intro C hC
    let := hC.2
    exact (commutator_eq_self (H := C)).symm.le.trans
      (commutator_mono (le_sSup hC) (le_sSup hC))
  let := hp
  let E' := E.subgroupOf X
  have hEp : IsPPerfect 2 E' := perfect_twoPerfect.of_surjective
    (subgroupOfEquivOfLe hEX).symm.toMonoidHom (subgroupOfEquivOfLe hEX).symm.surjective
  let Y := (fittingSubgroup G).subgroupOf X
  have hYY : Y.map X.subtype ≤ fittingSubgroup G := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  have hYodd : Odd (Nat.card Y) := by
    rw [Nat.card_congr (Y.equivMapOfInjective X.subtype X.subtype_injective).toEquiv]
    exact (fitting_odd_of_twoCore_eq_bot hc).of_dvd_nat (card_dvd_of_le hYY)
  have hgen : Y ⊔ E' = ⊤ := by
    apply top_unique
    intro x _
    have hxF : (x : G) ∈ fittingSubgroup G ⊔ componentLayer G := hXF x.property
    obtain ⟨f, hf, e, he, hfe⟩ := Subgroup.mem_sup_of_normal_left.mp hxF
    have hfX : f ∈ X := by
      have heq : f = (x : G) * e⁻¹ := by rw [← hfe]; group
      rw [heq]
      exact X.mul_mem x.property (X.inv_mem (hEX he))
    have hx : x = (⟨f, hfX⟩ : X) * ⟨e, hEX he⟩ := Subtype.ext hfe.symm
    rw [hx]
    exact (Y ⊔ E').mul_mem (mem_sup_left hf) (mem_sup_right he)
  apply (pResidual_eq_top_iff 2 X).mp
  apply top_unique
  rw [← hgen]
  exact sup_le (le_pResidual_of_isPPerfect Y (odd_twoPerfect hYodd))
    (le_pResidual_of_isPPerfect E' hEp)

/-- The exact two alternatives of A.4.4, for a subgroup of the quotient. -/
def IntersectionAlternative (X : Subgroup G) : Prop :=
  IsThetaSubgroup X ∨
    X ≤ generalizedFitting G ∧
    (X.subgroupOf (generalizedFitting G)).IsSubnormal ∧
    primeOrderGenerated (generalizedFitting G ⊓ centralizer (X : Set G)) ≤ X

private theorem alternative_data (hc : pCore 2 G = ⊥)
    (X : Subgroup G) (h : IntersectionAlternative X) :
    X.IsSubnormal ∧ IsPPerfect 2 X ∧ pCore 2 X = ⊥ := by
  have hXF : X ≤ generalizedFitting G := h.elim (fun h => h.le_generalizedFitting) And.left
  have hs : (X.subgroupOf (generalizedFitting G)).IsSubnormal :=
    h.elim (fun h => h.subnormal) (fun h => h.2.1)
  have hE : componentLayer G ≤ X := h.elim (fun h => h.layer_le)
    (fun h => layer_le_of_subnormal_prime_centralizer hc X h.1 h.2.1 h.2.2)
  have hsG : X.IsSubnormal := hs.trans hXF
    (inferInstance : (generalizedFitting G).Normal).isSubnormal
  refine ⟨hsG, twoPerfect_of_layer_le hc X hXF hE, ?_⟩
  have hh := pCoreAmbient_mono_of_isSubnormalIn X ⊤ 2 le_top hsG.subgroupOf
  change (pCore 2 X).map X.subtype ≤ (pCore 2 (⊤ : Subgroup G)).map
    (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom at hh
  rw [pCore_map_iso, hc] at hh
  exact (map_eq_bot_iff_of_injective _ X.subtype_injective).mp (bot_unique hh)

private theorem signalizer_eq_bot_of_alternative (hc : pCore 2 G = ⊥)
    (X R : Subgroup G) (h : IntersectionAlternative X)
    (hp : IsPGroup 2 R) (hn : X ≤ normalizer (R : Set G)) : R = ⊥ := by
  obtain ⟨hs, hperfect, hcore⟩ := alternative_data hc X h
  have hcomm := signalizer_commutator_le_pCore X ⊤ R le_top hs.subgroupOf
    hperfect ((isTwoSignalizer_iff X ⊤ R).mpr ⟨le_top, hp, hn⟩)
  rw [hcore, Subgroup.map_bot] at hcomm
  have hcentral : R ≤ centralizer (X : Set G) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (bot_unique hcomm))
  have hfaith : R ⊓ centralizer (X : Set G) = ⊥ := by
    rcases h with h | ⟨hXF, hsF, hprime⟩
    · exact lemma_G_8_9_2 hc h R hp
    · exact lemma_G_8_9_1 hc X R hXF hsF hprime hp
        (hcentral.trans (Subgroup.centralizer_le_normalizer _))
  rwa [inf_eq_left.mpr hcentral] at hfaith

private theorem quotient_twoCore_eq_bot : pCore 2 (G ⧸ pCore 2 G) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have he := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _)
    (show IsPGroup 2 q.ker by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  apply bot_unique
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) x
  exact (QuotientGroup.eq_one_iff g).mpr (he ▸ hx)

/-- The image X* under the literal quotient H → H/O₂(H). -/
def twoCoreQuotientImage (H X : Subgroup G) : Subgroup (H ⧸ pCore 2 H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))

/-- A.4.4(1), retaining the actual Θ and prime-order alternatives. -/
theorem lemma_A_4_4_1 (H K X : Subgroup G)
    (hcoreX : H.pCoreIn 2 ≤ X) (hXL : X ≤ H ⊓ K)
    (hX : IntersectionAlternative (twoCoreQuotientImage H X)) :
    H.pCoreIn 2 = (H ⊓ K).pCoreIn 2 := by
  let L := H ⊓ K
  let Q := L.pCoreIn 2
  have hQH : Q ≤ H := (pCoreIn_le 2 L).trans inf_le_left
  have hLN : L ≤ normalizer (Q : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hn : X.subgroupOf H ≤ normalizer (Q.subgroupOf H : Set H) := by
    apply le_normalizer_iff.mpr
    intro x hx q hq
    exact le_normalizer_iff.mp (hXL.trans hLN) (x : G) hx (q : G) hq
  let π := QuotientGroup.mk' (pCore 2 H)
  have hz : (Q.subgroupOf H).map π = ⊥ :=
    signalizer_eq_bot_of_alternative quotient_twoCore_eq_bot
      (twoCoreQuotientImage H X) ((Q.subgroupOf H).map π) hX
      (((isPGroup_pCoreIn 2 L).comap_subtype).map π)
      ((map_mono hn).trans (le_normalizer_map π))
  have hQcore : Q.subgroupOf H ≤ pCore 2 H := by
    simpa only [Subgroup.map_eq_bot_iff, π, QuotientGroup.ker_mk'] using hz
  apply le_antisymm
  · apply le_pCoreIn_inf (isPGroup_pCoreIn 2 H) (pCoreIn_le 2 H)
      (hcoreX.trans (hXL.trans inf_le_right))
    exact H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  · have hh := map_mono (f := H.subtype) hQcore
    rwa [map_subgroupOf_eq_of_le hQH] at hh

/-- O_{2,F*}(H), the embedded preimage of F*(H/O₂(H)). -/
def twoGeneralizedFittingPreimage (H : Subgroup G) : Subgroup G :=
  ((generalizedFitting (H ⧸ pCore 2 H)).comap
    (QuotientGroup.mk' (pCore 2 H))).map H.subtype

omit [Finite G] in
/-- The preimage convention has exactly the required quotient image. -/
theorem twoCoreQuotientImage_fittingPreimage (H : Subgroup G) :
    twoCoreQuotientImage H (twoGeneralizedFittingPreimage H) =
      generalizedFitting (H ⧸ pCore 2 H) := by
  unfold twoCoreQuotientImage twoGeneralizedFittingPreimage
  rw [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

omit [Finite G] in
/-- The source preimage contains O₂(H). -/
theorem twoCore_le_fittingPreimage (H : Subgroup G) :
    H.pCoreIn 2 ≤ twoGeneralizedFittingPreimage H := by
  apply map_mono
  intro x hx
  change QuotientGroup.mk' (pCore 2 H) x ∈ generalizedFitting (H ⧸ pCore 2 H)
  have he : QuotientGroup.mk' (pCore 2 H) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [he]
  exact one_mem _

/-- The relative version C(K,Q) of C.1.5: generation takes place in K. -/
def characteristicNormalizerIn (K Q : Subgroup G) : Subgroup G :=
  ⨆ (C : Subgroup Q) (_ : C.Characteristic) (_ : C ≠ ⊥),
    K ⊓ normalizer (C.map Q.subtype : Set G)

omit [Finite G] in
/-- At the full ambient group, this is the existing C(G,Q). -/
theorem characteristicNormalizerIn_top (Q : Subgroup G) :
    characteristicNormalizerIn ⊤ Q = characteristicNormalizerClosure Q := by
  simp only [characteristicNormalizerIn, characteristicNormalizerClosure, top_inf_eq]

omit [Finite G] in
private theorem core_normalized (H : Subgroup G) :
    H ≤ normalizer (H.pCoreIn 2 : Set G) :=
  H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))

omit [Finite G] in
private theorem maximal_core_ne_bot (H : Subgroup G) (hH : IsMaximalTwoLocal H) :
    H.pCoreIn 2 ≠ ⊥ := by
  obtain ⟨Q, hQ, hpQ, hHQ⟩ := hH.1
  have hQH : Q ≤ H := hHQ ▸ Q.le_normalizer
  have hQcore := le_pCoreIn_of_normalizes hpQ hQH hHQ.le
  exact fun he => hQ (bot_unique (he ▸ hQcore))

omit [Finite G] in
private theorem maximal_core_normalizer (H : Subgroup G) (hH : IsMaximalTwoLocal H) :
    H = normalizer (H.pCoreIn 2 : Set G) :=
  hH.eq_of_le ⟨H.pCoreIn 2, maximal_core_ne_bot H hH, isPGroup_pCoreIn 2 H, rfl⟩
    (core_normalized H)

omit [Finite G] in
private theorem maximal_core_characteristicNormalizerClosure (H : Subgroup G)
    (hH : IsMaximalTwoLocal H) : characteristicNormalizerClosure (H.pCoreIn 2) = H := by
  apply le_antisymm
  · apply (characteristicNormalizerClosure_le_iff _ _).mpr
    intro C hC hne
    let := hC
    have hmap : C.map (H.pCoreIn 2).subtype ≠ ⊥ := fun he =>
      hne ((map_eq_bot_iff_of_injective _ (H.pCoreIn 2).subtype_injective).mp he)
    have hn := (core_normalized H).trans
      (normalizer_le_normalizer_characteristic_image (H.pCoreIn 2) C)
    exact hH.2 ⟨_, hmap,
      ((isPGroup_pCoreIn 2 H).to_subgroup C).map (H.pCoreIn 2).subtype, rfl⟩ hn
  · exact (core_normalized H).trans
      (normalizer_le_characteristicNormalizerClosure_self _ (maximal_core_ne_bot H hH))

/-- A.4.4(2): characteristic normalizers in K lie in H ∩ K. -/
theorem lemma_A_4_4_2 (H K X : Subgroup G)
    (hcoreX : H.pCoreIn 2 ≤ X) (hXL : X ≤ H ⊓ K)
    (hX : IntersectionAlternative (twoCoreQuotientImage H X))
    (hH : IsMaximalTwoLocal H) :
    characteristicNormalizerIn K ((H ⊓ K).pCoreIn 2) ≤ H ⊓ K := by
  rw [← lemma_A_4_4_1 H K X hcoreX hXL hX]
  apply iSup_le
  intro C
  apply iSup_le
  intro hC
  apply iSup_le
  intro hne
  let := hC
  have hn : normalizer (C.map (H.pCoreIn 2).subtype : Set G) ≤ H := by
    exact (normalizer_le_characteristicNormalizerClosure _ C hne).trans
      (maximal_core_characteristicNormalizerClosure H hH).le
  exact le_inf (inf_le_right.trans hn) inf_le_left

/-- A.4.4(3): the full quotient generalized-Fitting preimage gives equality. -/
theorem lemma_A_4_4_3 (H K X : Subgroup G)
    (hcoreX : H.pCoreIn 2 ≤ X) (hXL : X ≤ H ⊓ K)
    (hX : IntersectionAlternative (twoCoreQuotientImage H X))
    (hH : IsMaximalTwoLocal H) (hK : IsMaximalTwoLocal K)
    (hKH : twoGeneralizedFittingPreimage K ≤ H) : H = K := by
  have hpreK : twoGeneralizedFittingPreimage K ≤ K := map_subtype_le _
  have ha : IntersectionAlternative (twoCoreQuotientImage K (twoGeneralizedFittingPreimage K)) := by
    rw [twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl, ?_, ?_⟩
    · exact (inferInstance :
        ((generalizedFitting (K ⧸ pCore 2 K)).subgroupOf
          (generalizedFitting (K ⧸ pCore 2 K))).Normal).isSubnormal
    · apply (closure_le _).mpr
      intro x hx
      exact hx.1.1
  have hcoreH := lemma_A_4_4_1 H K X hcoreX hXL hX
  have hcoreK := lemma_A_4_4_1 K H (twoGeneralizedFittingPreimage K)
    (twoCore_le_fittingPreimage K) (le_inf hpreK hKH) ha
  have he : H.pCoreIn 2 = K.pCoreIn 2 := by
    rw [hcoreH, hcoreK, inf_comm K H]
  rw [maximal_core_normalizer H hH, maximal_core_normalizer K hK, he]

omit [Finite G] in
/-- The generated-subgroup condition is exactly the source's elementwise clause. -/
theorem intersectionAlternative_iff (X : Subgroup G) :
    IntersectionAlternative X ↔ IsThetaSubgroup X ∨
      X ≤ generalizedFitting G ∧
      (X.subgroupOf (generalizedFitting G)).IsSubnormal ∧
      ∀ x : G, x ∈ generalizedFitting G → x ∈ centralizer (X : Set G) →
        (orderOf x).Prime → x ∈ X := by
  constructor
  · rintro (h | ⟨hXF, hs, hp⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hXF, hs, fun x hx hc hprime =>
        hp (Subgroup.subset_closure ⟨⟨hx, hc⟩, hprime⟩)⟩
  · rintro (h | ⟨hXF, hs, hp⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hXF, hs, (closure_le _).mpr
        (fun x hx => hp x hx.1.1 hx.1.2 hx.2)⟩

/-- All three clauses of Aschbacher–Smith A.4.4, printed p.58. -/
theorem lemma_A_4_4 (H K X : Subgroup G)
    (hcoreX : H.pCoreIn 2 ≤ X) (hXL : X ≤ H ⊓ K)
    (hX : IntersectionAlternative (twoCoreQuotientImage H X)) :
    H.pCoreIn 2 = (H ⊓ K).pCoreIn 2 ∧
    (IsMaximalTwoLocal H →
      characteristicNormalizerIn K ((H ⊓ K).pCoreIn 2) ≤ H ⊓ K) ∧
    (IsMaximalTwoLocal H → IsMaximalTwoLocal K →
      twoGeneralizedFittingPreimage K ≤ H → H = K) :=
  ⟨lemma_A_4_4_1 H K X hcoreX hXL hX,
    lemma_A_4_4_2 H K X hcoreX hXL hX,
    lemma_A_4_4_3 H K X hcoreX hXL hX⟩

end CFSG.Quasithin.ChapterA.Section04

end
