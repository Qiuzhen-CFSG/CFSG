module
public import Theory.GroupTheory.PResidual.PairedCentralizers
public import CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.NormalitySource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.PairedCentralizerSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonNormalCentralizers
public import Theory.SpecificGroups.PSL2.InvolutionFusion

/-!
# The paired residual calculation in the original nonnormal branch

Nonnormality forces the prime PSL₂ component family. Its involution
centralizers and outer automorphism group have two-power order, and its
involutions form one conjugacy class. The actual commuting conjugate pair
has centralizer of order prime to three. The paired residual theorem then
identifies O^{3′}(C_G(i)) with the companion component from precisely the
component-persistence hypothesis at i.

The terminal consumer derives normality of the original component from
2.5.19's persistence conclusion on C_S(K), transporting that conclusion
through the literal conjugation map. The residual calculation, tightness,
and final Sylow-normalizer contradiction are discharged here; the preceding
2.5.19 persistence remains a genuine earlier source obligation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
2.5.20, printed p.564.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
open ComponentSelection ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The literal paired involution residual from component persistence. -/
theorem source_paired_involution_residual
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hn : ¬ (K.subgroupOf H).Normal)
    (u : G) (hc : K ≤ centralizer (K.conjBy u : Set G))
    (i : G) (hiK : i ∈ K) (hi : orderOf i = 2)
    (hcomp : IsComponentIn (K.conjBy u) (centralizer ({i} : Set G))) :
    (primeToResidual 3 (centralizer ({i} : Set G))).map
      (centralizer ({i} : Set G)).subtype = K.conjBy u := by
  let L := K.conjBy u
  let iK : K := ⟨i, hiK⟩
  let eL : L ≃* K := ((MulAut.conj u).subgroupMap K).symm
  have hm := MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  let : IsSimpleGroup K := MathieuSourceSetup.component_simple c hG hempty hgen
  have hKr : primeToResidual 3 K = ⊤ := by
    rcases (inferInstance : (primeToResidual 3 K).Normal).eq_bot_or_eq_top with he | he
    · have hcop := primeToResidual_index_coprime (G := K) 3
      rw [he, index_bot] at hcop
      exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3)
        (dvd_refl 3) hm.three_dvd_card hcop).elim
    · exact he
  have hLr : primeToResidual 3 L = ⊤ := by
    have hh := map_primeToResidual (p := 3) eL.symm
    rw [hKr, map_top_of_surjective _ eL.symm.surjective] at hh
    exact hh.symm
  have hO : Nat.Coprime 3 (Nat.card (MulAut.Outer K)) := by
    obtain ⟨n, hn⟩ :=
      (MathieuSourceSetup.small_source_structure c hG hempty hgen hb).2.2.1.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  have hOL : Nat.Coprime 3 (Nat.card (MulAut.Outer L)) := by
    rwa [Nat.card_congr (MulAut.outerCongr eL).toEquiv]
  have hiK2 : orderOf iK = 2 := by simpa only [iK, Subgroup.orderOf_mk] using hi
  have hCi : Nat.Coprime 3 (Nat.card (centralizer ({iK} : Set K))) := by
    obtain ⟨n, hn⟩ :=
      (MathieuSourceSetup.nonnormal_component_involution_centralizer_isTwoGroup
        c hG hempty hgen hb hn iK hiK2).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  have hclass : ∀ a : MulAut K, IsConj (a iK) iK := by
    obtain ⟨p, hp, _, ⟨e⟩⟩ :=
      MathieuSourceSetup.nonnormal_component_prime_model c hG hempty hgen hb hn
    let : Fact p.Prime := ⟨hp.1⟩
    intro a
    have hh := Theory.PSL2.involutions_isConj (e (a iK)) (e iK)
      ((e.orderOf_eq _).trans ((a.orderOf_eq _).trans hiK2))
      ((e.orderOf_eq _).trans hiK2)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      e.symm.toMonoidHom.map_isConj hh
  have hcard : Nat.card (normalizer (K : Set G)) = Nat.card (normalizer (L : Set G)) := by
    dsimp only [L, Subgroup.conjBy]
    rw [← map_normalizer_eq_of_bijective K (MulAut.conj u).bijective,
      card_map_of_injective (MulAut.conj u).injective]
  exact paired_involution_centralizer_primeToResidual 3 K L iK hc hcomp.2.1 hLr hCi hO hOL
    (MathieuSourceSetup.companion_centralizer_coprime_three c hG hempty hgen hb u hc)
    hclass hcard

/-- Persistence for the companion on the original component Sylow excludes
the nonnormal branch, with its residual premise now proved. -/
theorem source_nonnormal_pair_persistence_false
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hn : ¬ (K.subgroupOf H).Normal)
    (u : G) (hu : u ∈ (S : Subgroup H).map H.subtype)
    (hc : K ≤ centralizer (K.conjBy u : Set G))
    (horbit : ∀ a ∈ (S : Subgroup H).map H.subtype,
      K.conjBy a = K ∨ K.conjBy a = K.conjBy u)
    (hcomp : ∀ i ∈ ((S : Subgroup H).map H.subtype ⊓ K : Subgroup G),
      orderOf i = 2 → IsComponentIn (K.conjBy u) (centralizer ({i} : Set G))) : False := by
  apply source_nonnormal_pair_residual_false c hG hempty hgen hb hn u hu hc horbit
  intro i hi hi2
  exact source_paired_involution_residual c hG hempty hgen hb hn u hc i hi.2 hi2
    (hcomp i hi hi2)

/-- Source 2.5.20 follows from precisely the component-persistence conclusion
of 2.5.19 on the original Sylow centralizer. -/
theorem source_component_normal_of_involution_persistence
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hpersist : ∀ i ∈ ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G) :
      Subgroup G), orderOf i = 2 → IsComponentIn K (centralizer ({i} : Set G))) :
    (K.subgroupOf H).Normal := by
  by_contra hn
  have hi := (source_component_normal_or_index_two hG.quasithin c.gamma
    ⟨c.component_le, c.component⟩).resolve_left hn
  obtain ⟨u, hu, hc, horbit⟩ := TwoComponentCenter.exists_two_component_orbit
    H K c.component_le c.component S hi
  apply source_nonnormal_pair_persistence_false c hG hempty hgen hb hn u hu hc horbit
  intro i hi hi2
  let Y := (S : Subgroup H).map H.subtype
  let e := MulAut.conj u
  let j := e.symm i
  have hjY : j ∈ Y := Y.mul_mem (Y.mul_mem (Y.inv_mem hu) hi.1) hu
  have hjC : j ∈ centralizer (K : Set G) := by
    intro k hk
    apply e.injective
    have hh := hc hi.2 (e k) (mem_map_of_mem e.toMonoidHom hk)
    simpa only [map_mul, j, MulEquiv.apply_symm_apply] using hh
  have hj2 : orderOf j = 2 := (e.symm.orderOf_eq i).trans hi2
  have hh := (hpersist j ⟨hjY, hjC⟩ hj2).map e
  have he : (centralizer ({j} : Set G)).map e.toMonoidHom =
      centralizer ({i} : Set G) := by
    simpa only [Set.image_singleton, j, MulEquiv.apply_symm_apply] using
      map_centralizer_equiv ({j} : Set G) e
  rwa [he] at hh

/-- The original 2.5.19(1) implication is sufficient for 2.5.20: in the
nonnormal branch it forces persistence at every relevant involution. -/
theorem source_component_normal_of_bad_involution_normal
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (h19 : ∀ i ∈ ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G) :
      Subgroup G), orderOf i = 2 →
      ¬ IsComponentIn K (centralizer ({i} : Set G)) → (K.subgroupOf H).Normal) :
    (K.subgroupOf H).Normal := by
  by_contra hn
  apply hn
  apply source_component_normal_of_involution_persistence c hG hempty hgen hb
  intro i hi hi2
  by_contra hbad
  exact hn (h19 i hi hi2 hbad)
end CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
