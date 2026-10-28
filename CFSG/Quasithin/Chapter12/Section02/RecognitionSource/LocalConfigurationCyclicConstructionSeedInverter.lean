module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSeedImage
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.InvertedHyperplane
public import Theory.GroupTheory.Involution.OddRotation

/-!
# Selecting the actual inverted prime conjugator

Baer–Suzuki applied inside the original moving H-star subgroup produces
a prime-order odd element inverted by an element of V outside O₂(H).
The proved order-two quotient image makes its conjugate pair a hyperplane
pair. Inversion puts the conjugator inside that literal generated pair.

This completes the prime-conjugator selection preceding 12.2.22. Selection
of an inverter-invariant Sylow subgroup, identification of the pair core,
noncyclic exclusion and final assembly remain with qt-d-12213-cyclic-block.
Source: Aschbacher–Smith, printed pp.802–803.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G} {d : ℕ}

/-- The original moving H-star subgroup supplies an actual inverted prime-order
conjugator and a hyperplane pair containing that conjugator. -/
theorem chosen_hstar_exists_inverted_prime_hyperplane_pair
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ p g v, p.Prime ∧ Odd p ∧
      g ∈ (pResidual 2 H).map H.subtype ∧ v ∈ V ∧ v ∉ H.pCoreIn 2 ∧
      orderOf g = p ∧ v * g * v⁻¹ = g⁻¹ ∧
      V ⊔ V.map (MulAut.conj g).toMonoidHom = zpowers g ⊔ V ∧
      Disjoint V (V.map (MulAut.conj g).toMonoidHom) ∧
      (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V = 2 := by
  let := D.elementary
  have hVH : V ≤ H := D.le_sylow.trans hH.1.1.2
  let E := V.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVH
  have hETI : IsTISubgroup E := by
    apply (isTISubgroup_iff E).mpr
    intro g hg x hx hgx
    apply Subtype.ext
    apply (isTISubgroup_iff V).mp hTI g ?_ x hx hgx
    intro hn
    exact hg (V.le_normalizer_comap H.subtype hn)
  obtain ⟨v, hv, hvQ⟩ := Set.not_subset.mp (A.hstar_movement H hH)
  let vH : H := ⟨v, hVH hv⟩
  have hvHQ : vH ∉ pCore 2 H := fun he => hvQ (mem_map_of_mem H.subtype he)
  have hvi : BenderSuzuki.PFAppendixIII.IsInvolution vH :=
    ⟨fun he => hvHQ (he ▸ (pCore 2 H).one_mem),
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv)⟩
  obtain ⟨p, hp, hp2, g, hg, hinv⟩ :=
    BenderSuzuki.involution_outside_twoCore_inverts_odd_prime vH hvi hvHQ
  have ho : Odd p := hp.odd_of_ne_two hp2
  have hgo : Odd (orderOf g) := hg.symm ▸ ho
  have hi : vH * g * vH⁻¹ = g⁻¹ := by
    simpa only [BenderSuzuki.PFAppendixIII.rightConjugateElem, hvi.inv_eq_self] using hinv
  have hgq : q g ≠ 1 := by
    intro he
    have hgcore : g ∈ pCore 2 H := (QuotientGroup.eq_one_iff g).mp he
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨g, hgcore⟩
    have hd : p ∣ 2 ^ n := hg ▸ orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hk : q.ker ≤ normalizer (E : Set H) := by
    rw [QuotientGroup.ker_mk']
    have hQT := (pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal (T.subtype hH.1.1.2)
    intro x hx
    exact V.le_normalizer_comap H.subtype (hT (hQT hx))
  have hiE := pair_normalizer_index_two_of_inverted_quotient_card_two E hETI q hk
    (chosen_hstar_quotient_module_card_two D A hT hTI hH) g vH hv
    (hgo.of_dvd_nat (orderOf_map_dvd q g)) hgq hi
  let B := V.map (MulAut.conj (g : G)).toMonoidHom
  have hBH : B ≤ H := by
    rintro x ⟨w, hw, rfl⟩
    exact H.mul_mem (H.mul_mem g.property (hVH hw)) (H.inv_mem g.property)
  have heB : E.map (MulAut.conj g).toMonoidHom = B.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom hw
    · rintro ⟨w, hw, hwe⟩
      exact ⟨⟨w, hVH hw⟩, hw, Subtype.ext hwe⟩
  rw [heB, ← subgroupOf_normalizer_eq hBH, relIndex_subgroupOf hVH] at hiE
  have hgG : orderOf (g : G) = p := (Subgroup.orderOf_coe g).trans hg
  have hiG : v * (g : G) * v⁻¹ = (g : G)⁻¹ := congrArg Subtype.val hi
  have hne : B ≠ V := by
    intro he
    rw [he, relIndex_eq_one.mpr V.le_normalizer] at hiE
    omega
  refine ⟨p, g, v, hp, ho, ?_, hv, hvQ, hgG, hiG, ?_, ?_, hiE⟩
  · exact mem_map_of_mem H.subtype
      (mem_pResidual_of_orderOf_coprime (Nat.coprime_two_left.mpr hgo))
  · exact conjugate_join_eq_cyclic_sup V g v hv (hgG.symm ▸ ho) hiG
  · exact ((hTI.eq_or_disjoint_conjugate g).resolve_left hne).symm

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
