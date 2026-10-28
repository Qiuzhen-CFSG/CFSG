module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Orbit
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Transport
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.PCoreImage

/-!
# The odd local-member orbit in E.1.11

For a local odd E-member P, its two-residual E modulo its own two-core
is a p-group for one odd prime p, and E is generated modulo that core by
commutators with the local actor. The conjugates of E under ambient tau
mutually normalize because they lie in components and the stabilizer fixes E.
Their two-cores generate a normal two-subgroup Q of the orbit overgroup;
the residual orbit modulo Q is a p-group.

The prescribed local Sylow intersection puts the seed two-core in T, hence
all its tau-conjugates and Q lie in T. The coprime index calculation then
constructs a Sylow subgroup of the orbit overgroup inside T, proving the
literal intersection assertion. Since ambient tau centralizes A when O₂(G)
is trivial, the seed commutator bound propagates to the orbit. Killing the
actual O₂(K_A) gives precisely the two quotient hypotheses of E.1.10(6).
The final theorems apply that result and the Sylow supplement of P.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed p.213.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem odd_core_residual {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hq : IsPGroup 2 (G ⧸ pCore p G)) : pResidual 2 G = pCore p G := by
  refine le_antisymm (sInf_le ⟨inferInstance, hq⟩) ?_
  apply le_sInf
  rintro N ⟨hN, hQ⟩
  let := hN
  let q := QuotientGroup.mk' N
  have hz : (pCore p G).map q = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne p 2 hp _ _ (pCore_isPGroup.map q) (hQ.to_subgroup _))
  simpa only [q, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz

omit [Finite G] in
private theorem quotient_pgroup_of_range {H : Type*} [Group H] {p : ℕ}
    (f : G →* H) (h : IsPGroup p f.range) (N : Subgroup G) [N.Normal]
    (hk : f.ker ≤ N) : IsPGroup p (G ⧸ N) := by
  have hq : IsPGroup p (G ⧸ f.ker) :=
    h.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  exact hq.of_surjective (QuotientGroup.map _ N (MonoidHom.id G) hk)
    (QuotientGroup.map_surjective_of_surjective _ N (MonoidHom.id G)
      QuotientGroup.mk_surjective hk)

private theorem residual_odd_data (V : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2)
    (hq : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ pCore p (G ⧸ pCore 2 G)))
    (hc : pCore p (G ⧸ pCore 2 G) = ⁅pCore p (G ⧸ pCore 2 G),
      V.map (QuotientGroup.mk' (pCore 2 G))⁆) :
    IsPGroup p (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) ∧
      pResidual 2 G ≤ ⁅pResidual 2 G, V⁆ ⊔ (pResidual 2 G).pCoreIn 2 := by
  let E := pResidual 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  have he : E.map q = pCore p (G ⧸ pCore 2 G) := by
    rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
    exact odd_core_residual hp hq
  have hk : (pCore 2 G).subgroupOf E ≤ pCore 2 E :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  constructor
  · let f := q.comp E.subtype
    have hker : f.ker ≤ pCore 2 E := by
      intro x hx
      exact hk ((QuotientGroup.eq_one_iff (x : G)).mp hx)
    have hr : f.range = E.map q := by rw [MonoidHom.range_comp, range_subtype]
    exact quotient_pgroup_of_range f (hr.symm ▸ he.symm ▸ pCore_isPGroup) _ hker
  · have hm : E.map q = (⁅E, V⁆).map q := by rw [map_commutator, he]; exact hc
    intro x hx
    obtain ⟨d, hd, hdx⟩ := hm ▸ mem_map_of_mem q hx
    have hdE : d ∈ E := commutator_le_left _ _ hd
    have hkE : d⁻¹ * x ∈ E := E.mul_mem (E.inv_mem hdE) hx
    have hkQ : d⁻¹ * x ∈ pCore 2 G := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (d⁻¹ * x) = 1
      rw [map_mul, map_inv, hdx, inv_mul_cancel]
    have hkC : d⁻¹ * x ∈ E.pCoreIn 2 :=
      mem_map_of_mem E.subtype (hk (show (⟨d⁻¹ * x, hkE⟩ : E) ∈
        (pCore 2 G).subgroupOf E from hkQ))
    simpa only [mul_inv_cancel_left] using
      (⁅E, V⁆ ⊔ E.pCoreIn 2).mul_mem (mem_sup_left hd) (mem_sup_right hkC)

omit [Finite G] in
private theorem image_pgroup_of_quotient {H : Type*} [Group H] {p q : ℕ}
    (B : Subgroup G) (f : G →* H)
    (h : IsPGroup p (B ⧸ pCore q B)) (hk : B.pCoreIn q ≤ f.ker) :
    IsPGroup p (B.map f) := by
  let g := f.subgroupMap B
  have hkg : pCore q B ≤ g.ker := by
    intro b hb
    apply Subtype.ext
    exact hk (mem_map_of_mem B.subtype hb)
  let gbar := QuotientGroup.lift (pCore q B) g hkg
  apply h.of_surjective gbar
  intro x
  obtain ⟨b, rfl⟩ := f.subgroupMap_surjective B x
  exact ⟨QuotientGroup.mk' (pCore q B) b, rfl⟩

omit [Finite G] in
private theorem quotient_iSup_pgroup {ι : Type*} {p q : ℕ}
    (B : ι → Subgroup G) (hB : ∀ i, (B i).Normal)
    (hgen : (⨆ i, B i) = ⊤) (Q : Subgroup G) [Q.Normal]
    (hquot : ∀ i, IsPGroup p ((B i) ⧸ pCore q (B i)))
    (hcore : ∀ i, (B i).pCoreIn q ≤ Q) : IsPGroup p (G ⧸ Q) := by
  let f := QuotientGroup.mk' Q
  have htop : (⊤ : Subgroup (G ⧸ Q)) ≤ pCore p (G ⧸ Q) := by
    rw [← map_top_of_surjective f (QuotientGroup.mk'_surjective Q), ← hgen,
      Subgroup.map_iSup]
    apply iSup_le
    intro i
    let _ : ((B i).map f).Normal := (hB i).map f (QuotientGroup.mk'_surjective Q)
    have hk : (B i).pCoreIn q ≤ f.ker := by simpa only [f, QuotientGroup.ker_mk'] using hcore i
    exact le_sSup ⟨inferInstance, image_pgroup_of_quotient (B i) f (hquot i) hk⟩
  exact (pCore_isPGroup.to_le htop).of_equiv topEquiv

private theorem component_orbit_core_quotient {p : ℕ}
    {J E U : Subgroup G} (hJ : IsComponent G J) (hEJ : E ≤ J)
    (hinv : U ⊓ normalizer (J : Set G) ≤ normalizer (E : Set G))
    (hquot : IsPGroup p (E ⧸ pCore 2 E)) :
    let N := componentOrbit E U
    let Q := componentOrbit (E.pCoreIn 2) U
    ∃ hn : (Q.subgroupOf N).Normal,
      @IsPGroup p (N ⧸ Q.subgroupOf N) (@QuotientGroup.Quotient.group N _ _ hn) := by
  let N := componentOrbit E U
  let Q := componentOrbit (E.pCoreIn 2) U
  obtain ⟨hQp, hQN, hKQ⟩ := hJ.local_core_orbit (p := 2) hEJ hinv
  have hNQ : N ≤ normalizer (Q : Set G) := (componentOrbit_le_sup E U).trans hKQ
  let _ : (Q.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNQ
  refine ⟨inferInstance, ?_⟩
  let B : U → Subgroup G := fun u => E.map (MulAut.conj (u : G)).toMonoidHom
  have hBN (u : U) : B u ≤ N := le_iSup B u
  have hNB (u : U) : N ≤ normalizer (B u : Set G) :=
    iSup_le fun v => hJ.local_conjugates_normalize hEJ hinv u v
  have hnorm (u : U) : ((B u).subgroupOf N).Normal :=
    normal_subgroupOf_of_le_normalizer (hNB u)
  have hgen : (⨆ u : U, (B u).subgroupOf N) = ⊤ := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_iSup]
    simp_rw [map_subgroupOf_eq_of_le (hBN _)]
    rw [← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hq (u : U) : IsPGroup p ((B u).subgroupOf N ⧸ pCore 2 ((B u).subgroupOf N)) := by
    let e : (B u).subgroupOf N ≃* E :=
      (subgroupOfEquivOfLe (hBN u)).trans ((MulAut.conj (u : G)).subgroupMap E).symm
    exact hquot.of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hc (u : U) : ((B u).subgroupOf N).pCoreIn 2 ≤ Q.subgroupOf N := by
    apply map_le_iff_le_comap.mp
    rw [map_pCoreIn_of_injective 2 _ _ N.subtype_injective,
      map_subgroupOf_eq_of_le (hBN u)]
    change (E.map (MulAut.conj (u : G)).toMonoidHom).pCoreIn 2 ≤ Q
    rw [← map_pCoreIn_of_injective 2 E _ (MulAut.conj (u : G)).injective]
    exact le_iSup (fun v : U => (E.pCoreIn 2).map (MulAut.conj (v : G)).toMonoidHom) u
  exact quotient_iSup_pgroup _ hnorm hgen _ hq hc

private theorem component_orbit_sylow (T : Sylow 2 G) {J E U : Subgroup G}
    (hJ : IsComponent G J) (hEJ : E ≤ J)
    (hinv : U ⊓ normalizer (J : Set G) ≤ normalizer (E : Set G))
    (hUT : U ≤ (T : Subgroup G)) (hcoreT : E.pCoreIn 2 ≤ (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hquot : IsPGroup p (E ⧸ pCore 2 E)) :
    ∃ R : Sylow 2 (componentOrbit E U ⊔ U : Subgroup G),
      (R : Subgroup _) = (T : Subgroup G).subgroupOf (componentOrbit E U ⊔ U) := by
  let N := componentOrbit E U
  let Q := componentOrbit (E.pCoreIn 2) U
  obtain ⟨hQp, hQN, hKQ⟩ := hJ.local_core_orbit (p := 2) hEJ hinv
  obtain ⟨hn, hq⟩ := component_orbit_core_quotient hJ hEJ hinv hquot
  let _ : (Q.subgroupOf N).Normal := hn
  have hQT : Q ≤ (T : Subgroup G) := by
    apply iSup_le
    intro u
    rintro _ ⟨x, hx, rfl⟩
    exact (T : Subgroup G).mul_mem
      ((T : Subgroup G).mul_mem (hUT u.property) (hcoreT hx))
      ((T : Subgroup G).inv_mem (hUT u.property))
  have hDT : Q ⊔ U ≤ (T : Subgroup G) := sup_le hQT hUT
  have hDN : Q ⊔ U ≤ normalizer (N : Set G) :=
    sup_le (hQN.trans N.le_normalizer) (le_normalizer_componentOrbit E U)
  have hindex : ¬ 2 ∣ (Q.subgroupOf N).index := by
    obtain ⟨m, hm⟩ := hq.exists_card_dvd_pow
    intro hd
    exact hp (Nat.prime_eq_prime_of_dvd_pow Nat.prime_two (Fact.out : p.Prime) (hd.trans hm)).symm
  obtain ⟨R, hR⟩ := IsPGroup.exists_sylow_sup_of_coprime_index N (Q ⊔ U)
    (T.isPGroup'.to_le hDT) hDN (Q.subgroupOf N) hindex
    (by rw [map_subgroupOf_eq_of_le hQN]; exact le_sup_left)
  have hjoin : N ⊔ (Q ⊔ U) = N ⊔ U := by
    rw [← sup_assoc, sup_eq_left.mpr hQN]
  let e := MulEquiv.subgroupCongr hjoin
  let R' : Sylow 2 (N ⊔ U : Subgroup G) := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR' : (R' : Subgroup _).map (N ⊔ U).subtype = Q ⊔ U := by
    change ((R : Subgroup _).map e.toMonoidHom).map (N ⊔ U).subtype = _
    rw [map_map]
    exact hR
  refine ⟨R', ?_⟩
  apply map_injective (N ⊔ U).subtype_injective
  rw [subgroupOf_map_subtype]
  exact (inf_eq_sylow_map R' T.isPGroup' (hR'.le.trans hDT)).symm

private theorem local_member_odd_seed {n : ℕ} (T : Sylow 2 G) (J A : Subgroup G)
    {P : Subgroup (localGroup T J)}
    (hP : IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P)
    (ho : ECaseOdd (A.subgroupOf (localGroup T J)) P) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      IsPGroup p (localMemberResidual T J P ⧸ pCore 2 (localMemberResidual T J P)) ∧
      localMemberResidual T J P ≤
        ⁅localMemberResidual T J P, A ⊓ normalizer (J : Set G)⁆ ⊔
          (localMemberResidual T J P).pCoreIn 2 ∧
      (localMemberResidual T J P).pCoreIn 2 ≤ (T : Subgroup G) := by
  let H := localGroup T J
  let V := A.subgroupOf H
  let E := pResidual 2 P
  let f := H.subtype.comp P.subtype
  have hf : Function.Injective f := H.subtype_injective.comp P.subtype_injective
  have hEf : E.map f = localMemberResidual T J P := by
    simp only [localMemberResidual, E, f, map_map, H]
  let e : E ≃* localMemberResidual T J P :=
    (E.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hEf)
  obtain ⟨p, hp, hpodd, hq, _, hc, _⟩ := ho
  let _ : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hpodd
  obtain ⟨heq, hec⟩ := residual_odd_data (V.subgroupOf P) hp2 hq hc
  refine ⟨p, hp, hp2, heq.of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)), ?_, ?_⟩
  · have hmap := map_mono (f := f) hec
    rw [Subgroup.map_sup, map_commutator, map_pCoreIn_of_injective 2 E f hf, hEf] at hmap
    have hVA : (V.subgroupOf P).map f ≤ A ⊓ normalizer (J : Set G) := by
      dsimp only [f]
      rw [← map_map, map_subgroupOf_eq_of_le hP.1.2.2.1]
      rw [subgroupOf_map_subtype]
      exact le_inf inf_le_left (inf_le_right.trans (sup_le J.le_normalizer inf_le_right))
    exact hmap.trans (sup_le_sup (commutator_mono le_rfl hVA) le_rfl)
  · rw [← hEf, ← map_pCoreIn_of_injective 2 E f hf]
    have hcore : E.pCoreIn 2 ≤ pCore 2 P :=
      le_sSup ⟨inferInstanceAs ((pCore 2 E).map E.subtype).Normal, isPGroup_pCoreIn 2 E⟩
    obtain ⟨R, hR⟩ := hP.1.2.2.2.2.1
    have hr : E.pCoreIn 2 ≤ (R : Subgroup P) :=
      hcore.trans (pCore_isPGroup.le_sylow_of_normal R)
    rintro _ ⟨x, hx, rfl⟩
    have hxR := hr hx
    rw [hR] at hxR
    exact hxR.1

omit [Finite G] in
private theorem range_pgroup_of_quotient {H : Type*} [Group H] {p : ℕ}
    (f : G →* H) (Q : Subgroup G) [Q.Normal]
    (h : IsPGroup p (G ⧸ Q)) (hk : Q ≤ f.ker) : IsPGroup p f.range := by
  let g := QuotientGroup.lift Q f.rangeRestrict (by simpa using hk)
  apply h.of_surjective g
  intro y
  obtain ⟨x, rfl⟩ := f.rangeRestrict_surjective y
  exact ⟨QuotientGroup.mk' Q x, rfl⟩

omit [Finite G] in
private theorem orbit_commutator_mod_core {E U A V : Subgroup G}
    (hseed : E ≤ ⁅E, V⁆ ⊔ E.pCoreIn 2) (hVA : V ≤ A)
    (hUA : U ≤ centralizer (A : Set G)) :
    componentOrbit E U ≤ ⁅componentOrbit E U, A⁆ ⊔ componentOrbit (E.pCoreIn 2) U := by
  apply iSup_le
  intro u
  have hmap := map_mono (f := (MulAut.conj (u : G)).toMonoidHom) hseed
  rw [Subgroup.map_sup, map_commutator] at hmap
  apply hmap.trans
  apply sup_le_sup
  · apply commutator_mono (le_iSup (fun v : U => E.map (MulAut.conj (v : G)).toMonoidHom) u)
    have he : A.map (MulAut.conj (u : G)).toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) (hUA u.property))
    exact (map_mono hVA).trans he.le
  · exact le_iSup (fun v : U => (E.pCoreIn 2).map (MulAut.conj (v : G)).toMonoidHom) u

/-- The odd branch provides the actual Sylow intersection and the two required
facts in the literal two-core quotient of the residual-orbit group. -/
theorem memberOrbitGroup_odd_data {n : ℕ} (T : Sylow 2 G) {J A : Subgroup G}
    (hcore : pCore 2 G = ⊥)
    (hX : ChiefFactor.IsChief (pResidual 2 G) ⊥)
    (hJ : IsComponentIn J (pResidual 2 G))
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    {P : Subgroup (localGroup T J)}
    (hP : IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P)
    (ho : ECaseOdd (A.subgroupOf (localGroup T J)) P) :
    let K := memberOrbitGroup T J A P
    (∃ R : Sylow 2 K, (R : Subgroup K) = (T : Subgroup G).subgroupOf K) ∧
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        IsPGroup p ((pResidual 2 K).map (QuotientGroup.mk' (pCore 2 K))) ∧
        (pResidual 2 K).map (QuotientGroup.mk' (pCore 2 K)) =
          ⁅(pResidual 2 K).map (QuotientGroup.mk' (pCore 2 K)),
            (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))⁆ := by
  let E := localMemberResidual T J P
  let U := tau (T : Subgroup G) A
  let N := memberResidualOrbit T J A P
  let K := memberOrbitGroup T J A P
  let Q := componentOrbit (E.pCoreIn 2) U
  have hNK : N ≤ K := le_sup_left
  have hJG : IsComponent G J :=
    ⟨hJ.2.1.trans hJ.1 hX.normal_upper.isSubnormal, hJ.quasisimple⟩
  have hEJ : E ≤ J := localMemberResidual_le_component T J P
  have hinv := memberResidual_stabilizer_invariant T J A hcore hP
  obtain ⟨p, hp, hp2, hquot, hseed, hcoreT⟩ := local_member_odd_seed T J A hP ho
  let _ : Fact p.Prime := ⟨hp⟩
  have hR := component_orbit_sylow T hJG hEJ hinv (tau_le _ _) hcoreT hp2 hquot
  have hQcore : Q ≤ K.pCoreIn 2 := by
    have hh := hJG.local_core_orbit_le (p := 2) hEJ hinv
    rw [← componentOrbit_sup E U] at hh
    exact hh
  have hres : pResidual 2 K = N.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le hNK]
    exact memberOrbitGroup_residual T J A P
  refine ⟨hR, p, hp, hp2, ?_, ?_⟩
  · obtain ⟨hn, hq⟩ := component_orbit_core_quotient hJG hEJ hinv hquot
    let _ : (Q.subgroupOf N).Normal := hn
    let f := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hNK)
    have hk : Q.subgroupOf N ≤ f.ker := by
      intro x hx
      apply (QuotientGroup.eq_one_iff (inclusion hNK x)).mpr
      obtain ⟨y, hy, he⟩ := hQcore hx
      exact (Subtype.ext he : y = inclusion hNK x) ▸ hy
    have hr := range_pgroup_of_quotient f (Q.subgroupOf N) hq hk
    have he : f.range = (pResidual 2 K).map (QuotientGroup.mk' (pCore 2 K)) := by
      rw [hres]
      simp only [f, MonoidHom.range_comp, inclusion_range]
    exact he ▸ hr
  · have hUA : U ≤ centralizer (A : Set G) := by
      intro u hu
      obtain ⟨_, hc⟩ := mem_centralizerModulo_iff.mp hu
      apply mem_centralizer_iff.mpr
      intro a ha
      exact commutatorElement_eq_one_iff_mul_comm.mp (mem_bot.mp (hcore ▸ hc a ha))
    have hNA : N ≤ ⁅N, A⁆ ⊔ K.pCoreIn 2 :=
      (orbit_commutator_mod_core hseed inf_le_left hUA).trans (sup_le_sup le_rfl hQcore)
    have hAK : A ≤ K :=
      ((le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans (tau_le_memberOrbitGroup T J A P))
    have hc : pResidual 2 K ≤ ⁅pResidual 2 K, A.subgroupOf K⁆ ⊔ pCore 2 K := by
      apply (map_le_map_iff_of_injective K.subtype_injective).mp
      rw [Subgroup.map_sup, map_commutator, memberOrbitGroup_residual,
        map_subgroupOf_eq_of_le hAK]
      exact hNA
    apply le_antisymm ?_ (commutator_le_left _ _)
    have hm := map_mono (f := QuotientGroup.mk' (pCore 2 K)) hc
    simpa only [Subgroup.map_sup, map_commutator, QuotientGroup.map_mk'_self, sup_bot_eq] using hm

/-- E.1.11, odd local-member branch: E.1.10(6) applies to the actual orbit
and its Sylow intersection, with no extra quotient or generation premise. -/
theorem memberOrbitGroup_le_generationTarget_of_odd {n : ℕ} (hn : 0 < n)
    (T : Sylow 2 G) {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    {J A : Subgroup G} (hcore : pCore 2 G = ⊥)
    (hX : ChiefFactor.IsChief (pResidual 2 G) ⊥)
    (_hna : ¬ IsMulCommutative (pResidual 2 G)) (hJ : IsComponentIn J (pResidual 2 G))
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    {P : Subgroup (localGroup T J)}
    (hP : IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P)
    (ho : ECaseOdd (A.subgroupOf (localGroup T J)) P) :
    memberOrbitGroup T J A P ≤ generationTarget n T Ω := by
  let _ := hΩ.1 A hA
  obtain ⟨⟨R, hR⟩, p, hp, hp2, hodd, hcomm⟩ :=
    memberOrbitGroup_odd_data T hcore hX hJ hAT hP ho
  let _ : Fact p.Prime := ⟨hp⟩
  exact le_generationTarget_of_odd_residual_quotient hn T hΩ hA hAT
    (memberOrbitGroup T J A P) R hR (tau_le_memberOrbitGroup T J A P) hp2 hodd hcomm

/-- The complete local member lies in the target by its prescribed Sylow
supplement; containment of P in its residual-orbit group is unnecessary. -/
theorem local_member_le_generationTarget_of_odd {n : ℕ} (hn : 0 < n)
    (T : Sylow 2 G) {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    {J A : Subgroup G} (hcore : pCore 2 G = ⊥)
    (hX : ChiefFactor.IsChief (pResidual 2 G) ⊥)
    (hna : ¬ IsMulCommutative (pResidual 2 G)) (hJ : IsComponentIn J (pResidual 2 G))
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    {P : Subgroup (localGroup T J)}
    (hP : IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P)
    (ho : ECaseOdd (A.subgroupOf (localGroup T J)) P) :
    P.map (localGroup T J).subtype ≤ generationTarget n T Ω :=
  local_member_le_of_orbitGroup_le T J A hP
    ((sylow_le_weakClosure_normalizer T hΩ).trans le_sup_right)
    (memberOrbitGroup_le_generationTarget_of_odd hn T hΩ hcore hX hna hJ hA hAT hP ho)

end CFSG.Quasithin.ChapterE.ChiefOrbit
