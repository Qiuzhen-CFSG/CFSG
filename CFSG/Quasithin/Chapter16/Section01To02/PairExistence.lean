module

public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.Quasithin.Chapter1.Section01
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# A component at a central involution: the existence reduction

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, Lemma 16.2.1, printed p.1173 (PDF p.1190).

Failure of even characteristic supplies a maximal two-local M containing a
chosen Sylow two-subgroup T. Its nontrivial two-core meets Ω₁(Z(T)), giving an
involution z. Maximality gives M = N_G(O₂(M)). The normalizer case of source
1.1.3(2) then transfers failure of characteristic two to C_G(z). Finally (E1)
and generalized-Fitting self-centralization force a nontrivial layer and an
actual component of C_G(z).

The local detection argument uses C_M(O₂(M)): it is normal in M, its two-core
maps into O₂(M), and characteristic two in an overgroup of this centralizer
would force M itself to have characteristic two. This proves the implication
needed from the source's O²(F*) calculation directly with self-centralizing
cores; no residual is identified with a core.

The normalizer inheritance assertion remains an explicit earlier input in the
last theorem. It is owned by the source 1.1.3 development. Thus this module
proves the independent witness construction and conditional assembly, not yet
the unconditional Lemma 16.2.1. No model facts or component witnesses are
assumed by Hypothesis 16.1.1 here.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.PairExistence
variable {G : Type*} [Group G] [Finite G]

private theorem characteristicTwo_of_core_centralizer_le
    (H : Subgroup G) (hH : HasCharacteristicTwo H)
    (hle : centralizer (pCore 2 G : Set G) ≤ H) : HasCharacteristicTwo G := by
  let C := centralizer (pCore 2 G : Set G)
  have hC : HasCharacteristicTwo C :=
    HasCharacteristicTwo.of_equiv (subgroupOfEquivOfLe hle)
      (normal_core_selfCentralizing hH (C.subgroupOf H))
  have hcore : (pCore 2 C).map C.subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map C.subtype⟩
  have htop : (⊤ : Subgroup C) ≤ pCore 2 C := by
    intro c _
    apply hC
    apply mem_centralizer_iff.mpr
    intro q hq
    exact Subtype.ext ((mem_centralizer_iff.mp c.property) q
      (hcore (mem_map.mpr ⟨q, hq, rfl⟩)))
  intro c hc
  exact hcore (mem_map.mpr ⟨⟨c, hc⟩, htop (mem_top _), rfl⟩)

private theorem characteristicTwo_of_centralizer_core_element
    (z : G) (hz : z ∈ pCore 2 G)
    (hC : HasCharacteristicTwo (centralizer ({z} : Set G))) :
    HasCharacteristicTwo G := by
  apply characteristicTwo_of_core_centralizer_le _ hC
  exact centralizer_le (Set.singleton_subset_iff.mpr hz)

omit [Finite G] in
private theorem maximalTwoLocal_normalizer_core {M : Subgroup G}
    (hM : IsMaximalTwoLocal M) :
    normalizer (M.pCoreIn 2 : Set G) = M := by
  have hne : M.pCoreIn 2 ≠ ⊥ := Chapter1.mem_H_of_isTwoLocal hM.1
  have hMN : M ≤ normalizer (M.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 M).le_normalizer_map M.subtype
  exact le_antisymm (hM.2 ⟨M.pCoreIn 2, hne, isPGroup_pCoreIn 2 M, rfl⟩ hMN) hMN

private theorem exists_central_involution_in_core
    (T : Sylow 2 G) {M : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M) :
    ∃ z : T, orderOf z = 2 ∧ z ∈ omegaOneAmbient (center T) ∧
      (z : G) ∈ M.pCoreIn 2 := by
  let Q := M.pCoreIn 2
  have hQne : Q ≠ ⊥ := Chapter1.mem_H_of_isTwoLocal hM.1
  have hQT : Q ≤ (T : Subgroup G) := by
    have hc := pCoreIn_le_sylow M (T.subtype hTM)
    exact hc.trans (by rintro x ⟨y, hy, rfl⟩; exact hy)
  have hTN : (T : Subgroup G) ≤ normalizer (Q : Set G) := by
    rw [maximalTwoLocal_normalizer_core hM]
    exact hTM
  let N := Q.subgroupOf (T : Subgroup G)
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hQT).mpr hTN
  let : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr hQne
  have hN : Nontrivial N := (subgroupOfEquivOfLe hQT).nontrivial
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨Z, _, hZN, hZcard, hZcenter⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N hN
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZcard])
  have hzT : orderOf (z : T) = 2 := (orderOf_coe z).trans hz
  refine ⟨z, hzT, ?_, hZN z.property⟩
  exact (omegaOneAmbient_le_iff (center T) (omegaOneAmbient (center T))).mp le_rfl
    z (hZcenter z.property) (by simpa only [hzT] using pow_orderOf_eq_one (z : T))

/-- The maximal local witness and a central involution in its two-core. -/
theorem exists_bad_maximalTwoLocal_central_involution
    (h : ¬ IsEvenCharacteristic G) (T : Sylow 2 G) :
    ∃ (M : Subgroup G) (z : T), IsMaximalTwoLocal M ∧ (T : Subgroup G) ≤ M ∧
      ¬ HasCharacteristicTwo M ∧ normalizer (M.pCoreIn 2 : Set G) = M ∧
      orderOf z = 2 ∧ z ∈ omegaOneAmbient (center T) ∧
      (z : G) ∈ M.pCoreIn 2 := by
  have hbad : ∃ M : Subgroup G, IsMaximalTwoLocal M ∧ (T : Subgroup G) ≤ M ∧
      ¬ HasCharacteristicTwo M := by
    by_contra! hn
    exact h (IsEvenCharacteristicAt.all hn)
  obtain ⟨M, hM, hTM, hbad⟩ := hbad
  obtain ⟨z, hz, hzc, hzQ⟩ := exists_central_involution_in_core T hM hTM
  exact ⟨M, z, hM, hTM, hbad, maximalTwoLocal_normalizer_core hM, hz, hzc, hzQ⟩

/-- Failure at a core element transfers through the normalizer case of 1.1.3(2). -/
theorem not_characteristicTwo_centralizer_of_normalizer_inheritance
    (inheritance : ∀ (H : Subgroup G) (X : Subgroup H), IsPGroup 2 X →
      HasCharacteristicTwo H → HasCharacteristicTwo (normalizer (X : Set H)))
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hbad : ¬ HasCharacteristicTwo M)
    {z : G} (hzQ : z ∈ M.pCoreIn 2)
    (hQC : M.pCoreIn 2 ≤ involutionCentralizer z) :
    ¬ HasCharacteristicTwo (involutionCentralizer z) := by
  intro hC
  let C := involutionCentralizer z
  let Q := M.pCoreIn 2
  have hn := inheritance C (Q.subgroupOf C) (isPGroup_pCoreIn 2 M).comap_subtype hC
  have hnorm : normalizer (Q.subgroupOf C : Set C) = M.subgroupOf C := by
    rw [← subgroupOf_normalizer_eq hQC, maximalTwoLocal_normalizer_core hM]
  rw [hnorm] at hn
  have hzM : z ∈ M := pCoreIn_le 2 M hzQ
  let zM : M := ⟨z, hzM⟩
  have he : centralizer ({zM} : Set M) ≃* M.subgroupOf C :=
    { toFun := fun x => ⟨⟨x, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x, x.property⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  apply hbad
  apply characteristicTwo_of_centralizer_core_element zM
  · obtain ⟨x, hx, heq⟩ := hzQ
    exact (Subtype.ext heq : x = zM) ▸ hx
  · exact hn.of_equiv he.symm

/-- E1 and a bad central involution centralizer give an actual component. -/
theorem exists_setup_of_not_characteristicTwo
    (h : HasEvenTypeCentralizers G) (T : Sylow 2 G) {z : G}
    (hz : orderOf z = 2) (hzT : z ∈ T)
    (hTC : (T : Subgroup G) ≤ involutionCentralizer z)
    (hbad : ¬ HasCharacteristicTwo (involutionCentralizer z)) :
    ∃ L : Subgroup G, CentralComponentSetup T z L := by
  let C := involutionCentralizer z
  have hF : generalizedFitting C ≠ pCore 2 C := by
    intro he
    apply hbad
    change centralizer (pCore 2 C : Set C) ≤ pCore 2 C
    rw [← he]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hE : componentLayer C ≠ ⊥ := by
    intro he
    apply hF
    rw [generalizedFitting, he, sup_bot_eq, Fitting_eq_pcore C 2 (h.oddCore z hz)]
  have hex : ∃ D : Subgroup C, IsComponent C D := by
    by_contra! hn
    apply hE
    apply sSup_eq_bot.mpr
    intro D hD
    exact (hn D hD).elim
  obtain ⟨D, hD⟩ := hex
  refine ⟨D.map C.subtype, hz, hzT, hTC, map_subtype_le D, ?_⟩
  change IsComponent C ((D.map C.subtype).comap C.subtype)
  rw [comap_map_eq_self_of_injective C.subtype_injective]
  exact hD

/-- Conditional assembly of 16.2.1. The earlier normalizer inheritance theorem
is the only remaining input; it is not assumed in Hypothesis 16.1.1. -/
theorem centralComponentPairs_nonempty_of_normalizer_inheritance
    {K : GroupClass} (h : Hypothesis1611 K G)
    (inheritance : ∀ (H : Subgroup G) (X : Subgroup H), IsPGroup 2 X →
      HasCharacteristicTwo H → HasCharacteristicTwo (normalizer (X : Set H))) :
    (centralComponentPairs (G := G)).Nonempty := by
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 G))
  obtain ⟨M, z, hM, hTM, hbad, _, hz, hzc, hzQ⟩ :=
    exists_bad_maximalTwoLocal_central_involution h.not_evenCharacteristic T
  have hTC : (T : Subgroup G) ≤ involutionCentralizer (z : G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_center_iff.mp (omegaOneAmbient_le (center T) hzc) ⟨t, ht⟩))
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hc := pCoreIn_le_sylow M (T.subtype hTM)
    exact hc.trans (by rintro x ⟨y, hy, rfl⟩; exact hy)
  have hc := not_characteristicTwo_centralizer_of_normalizer_inheritance
    inheritance hM hbad hzQ (hQT.trans hTC)
  obtain ⟨L, hL⟩ := exists_setup_of_not_characteristicTwo h.evenType T
    ((orderOf_coe z).trans hz) z.property hTC hc
  exact ⟨((z : G), L), T, hL⟩

end CFSG.Quasithin.Chapter16.PairExistence
