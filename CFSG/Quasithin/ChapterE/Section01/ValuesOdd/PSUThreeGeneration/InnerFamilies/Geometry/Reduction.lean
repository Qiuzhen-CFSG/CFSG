module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerActors
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.QuotientLifting.OddSections
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# Local odd subgroups in the inner PSU₃ geometry

An odd-prime subgroup normalized by the actual ambient tau contributes its
actor commutator to the obstruction overgroup. In the join with tau, the odd
subgroup is normal and tau is Sylow, by the coprime product order. The proved
hyperplane E-generation and E-member inheritance then give ambient containment.
No assertion of global normality or closure of the source family is needed.

If the involution centralizer is maximal inside the normal socle, the supplied
ambient centralizer containment identifies the proper obstruction overgroup
with that centralizer. The remaining model geometry must move the central
involution either by a solvable Sylow overgroup or by an odd commutator of the
kind just described. These matrix constructions and intrinsic maximality are
explicit premises below, not consequences asserted by this reduction.

Source: Aschbacher--Smith, E.1.8(2), E.1.10(6)--(8), E.1.13 and E.1.14(7),
printed pp.211--214; A.3.21, p.55; Aschbacher, *GF(2)-representations of finite
groups* (1982), Lemma 4.11.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The commutator of an odd-prime subgroup normalized by the literal ambient tau
lies in the obstruction. Normality is needed only in the local join with tau;
the odd subgroup need not be normal in G or normalized by all of T. -/
theorem tau_normalized_odd_commutator_le {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    {r : ℕ} [Fact r.Prime] (hr : r ≠ 2) (X : Subgroup G)
    (hX : IsPGroup r X)
    (hn : tau (T : Subgroup G) A ≤ normalizer (X : Set G)) :
    ⁅X, A⁆ ≤ d.overgroup := by
  let := d.elementary.1 A hA
  let R := tau (T : Subgroup G) A
  let H := X ⊔ R
  have hRT : R ≤ (T : Subgroup G) := tau_le _ _
  have hR : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hAR : A ≤ R := le_sup_left.trans (sup_pCore_le_tau T A hAT)
  have hAH : A ≤ H := hAR.trans le_sup_right
  have hXH : X ≤ H := le_sup_left
  have hRH : R ≤ H := le_sup_right
  let : (X.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hn)
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have hdisj : Disjoint X R := IsPGroup.disjoint_of_ne r 2 hr X R hX hR
  have hcard : Nat.card H = Nat.card X * Nat.card R := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes X R hn
    simpa only [hdisj.eq_bot, card_bot, one_mul] using hh.symm
  have hRcard : Nat.card (R.subgroupOf H) = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv
  have hindex : (R.subgroupOf H).index = Nat.card X := by
    have hh := (R.subgroupOf H).card_mul_index
    rw [hRcard, hcard] at hh
    have hpos : 0 < Nat.card R := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (hh.trans (Nat.mul_comm _ _))
  have hXodd : ¬ 2 ∣ Nat.card X := by
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    rw [hn]
    exact Nat.prime_two.coprime_iff_not_dvd.mp
      (((Nat.coprime_primes Nat.prime_two (Fact.out : r.Prime)).mpr hr.symm).pow_right n)
  let S : Sylow 2 H := hR.comap_subtype.toSylow (by
    change ¬ 2 ∣ (R.subgroupOf H).index
    rwa [hindex])
  have hTS : T.subgroupOf H = (S : Subgroup H) :=
    S.is_maximal' T.isPGroup'.comap_subtype (by intro x hx; exact hRT hx)
  have hc := odd_normal_commutator_le_eSubgroup_one hr S
    (X.subgroupOf H) (A.subgroupOf H) hX.comap_subtype
    (by rw [← hTS]; exact comap_mono hAT)
  have hm : (eSubgroup 1 (S : Subgroup H) (A.subgroupOf H)).map H.subtype ≤
      d.overgroup := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro K hK
    rw [← hTS] at hK
    exact map_le_iff_le_comap.mp (d.members_le A hA hAT _
      (hK.inherit T A H hAT hRH))
  have h := (map_mono (f := H.subtype) hc).trans hm
  rwa [map_commutator, map_subgroupOf_eq_of_le hXH,
    map_subgroupOf_eq_of_le hAH] at h

/-- Intrinsic maximality of the socle centralizer determines every proper
obstruction overgroup containing the ambient centralizer. The normal-socle
product decomposition retains arbitrary two-extensions. -/
theorem overgroup_eq_centralizer_of_intrinsic_coatom (L : Subgroup G) [L.Normal] {T : Sylow 2 G}
    (hLT : L ⊔ (T : Subgroup G) = ⊤) (d : LargeFamilyObstruction T)
    (z : G) (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup)
    (hmax : IsCoatom ((centralizer ({z} : Set G)).subgroupOf L)) :
    d.overgroup = centralizer ({z} : Set G) := by
  have hML : d.overgroup.subgroupOf L ≠ ⊤ := by
    intro h
    have hLM : L ≤ d.overgroup := by
      intro l hl
      exact (show (⟨l, hl⟩ : L) ∈ d.overgroup.subgroupOf L from h.symm ▸ mem_top _)
    exact d.proper (top_unique (hLT ▸ sup_le hLM d.sylow_le))
  have he : d.overgroup.subgroupOf L = (centralizer ({z} : Set G)).subgroupOf L :=
    (hmax.le_iff_eq hML).mp (comap_mono hCM)
  apply le_antisymm _ hCM
  intro g hg
  obtain ⟨l, hl, t, ht, rfl⟩ := mem_sup_of_normal_left.mp (hLT.symm ▸ mem_top g)
  have hlM : l ∈ d.overgroup := by
    have hh := d.overgroup.mul_mem hg (d.overgroup.inv_mem (d.sylow_le ht))
    simpa using hh
  have hlC : l ∈ centralizer ({z} : Set G) := by
    exact (show (⟨l, hl⟩ : L) ∈ (centralizer ({z} : Set G)).subgroupOf L from
      he ▸ hlM)
  exact mul_mem hlC (hTz ht)

/-- Source application of the local odd argument. If the model supplies
intrinsic maximality of the involution centralizer, every solvable Sylow
overgroup and every odd commutator normalized by the centralizer of an inner
actor must centralize that involution. The actor is selected from the original
family, without discarding any outer members or adding subgroups to it. -/
theorem constraints_of_intrinsic_coatom [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T)
    (hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧
      A ≤ generalizedFitting G)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup)
    (hmax : IsCoatom ((centralizer ({z} : Set G)).subgroupOf (generalizedFitting G))) :
    normalizer (weakClosure (T : Subgroup G) d.family : Set G) ≤
        centralizer ({z} : Set G) ∧
      (∀ H : Subgroup G, (T : Subgroup G) ≤ H → Group.IsSolvable H →
        H ≤ centralizer ({z} : Set G)) ∧
      ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≤ generalizedFitting G ∧
        Nat.card A = 4 ∧ z ∈ A ∧
        ∀ (r : ℕ), r.Prime → Odd r → ∀ X : Subgroup G, IsPGroup r X →
          (T : Subgroup G) ⊓ centralizer (A : Set G) ≤ normalizer (X : Set G) →
          ⁅X, A⁆ ≤ centralizer ({z} : Set G) := by
  have hMC := overgroup_eq_centralizer_of_intrinsic_coatom (generalizedFitting G)
    hLT d z hTz hCM hmax
  refine ⟨hMC ▸ d.normalizer_le, ?_, ?_⟩
  · intro H hTH hs
    let := hs
    exact hMC ▸ solvable_sylow_overgroup_le d H hTH
  · obtain ⟨A, hA, hAT, hne, hAL⟩ := hi
    have hzA := inner_member_contains_central_involution (generalizedFitting G)
      hp hodd hmodel d hA hAT hne hAL hzL (hz ▸ pow_orderOf_eq_one z) hTz
    refine ⟨A, hA, hAT, hAL,
      inner_member_card_eq_four (generalizedFitting G) hp hodd hmodel d hA hAT hne hAL,
      hzA, ?_⟩
    have hcore : pCore 2 G = ⊥ :=
      (SimpleSocle.structure_of_sylow_supplement
        (nonabelian_of_model hp hodd hmodel) T hLT).2.2.1
    have htau : tau (T : Subgroup G) A ≤
        (T : Subgroup G) ⊓ centralizer (A : Set G) := by
      intro t ht
      refine ⟨tau_le _ _ ht, mem_centralizer_iff.mpr ?_⟩
      intro a ha
      have hc := (mem_centralizerModulo_iff.mp ht).2 a ha
      rw [hcore, mem_bot] at hc
      exact commutatorElement_eq_one_iff_mul_comm.mp hc
    intro r hr ho X hX hn
    let : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ dvd_rfl)
    exact hMC ▸ tau_normalized_odd_commutator_le d hA hAT hr2 X hX (htau.trans hn)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry
