module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentsFitting
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Marker
public import Theory.GroupTheory.NormalizedSupConsequences
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.SourceInterface

/-!
# Invariant solvable subgroups in the constrained source catalogue

Original 15.1.19(2) controls every M_Z-invariant subgroup K of the fixed G₁
with F*(K)=O₂(K) and K=O₂,₂′(K). Its two-core lies in Q₁ by Sylow
maximality. The group KQ₁ is solvable and has characteristic two, so the
proved C.2.5/C.2.6 solvable block decomposition applies with Sylow Q₁.

Every A₃ factor is normalized by O²(M_Z): its full conjugacy family has
at most two members. The action on its cyclic three-quotient is trivial,
so it normalizes O²(M_Z). Original 15.1.18(7)'s residual-normalizer control
then places that factor in M_Z, eliminating every outside factor.

The source applications retain the original marker, unrestricted prime,
fixed G₁,M_Z,S,Q₁ and both exchanged-plane sizes. No characteristic-two
hypothesis on G₁ or C-component hypothesis on K is imposed. The literal
lower mixed-core preimage and its odd-quotient form are both exported.
The original 15.1.14 residual premise remains for
qt-e-1514-global-thompson-residual and its pre-exclusion assembly owner.
This supplies the control step for the orbit Borel in 15.1.20; constructing
that orbit's invariance and normal Sylow subgroup remains separate work.

Source: Aschbacher--Smith 15.1.19(2) and the third paragraph of 15.1.20,
printed pp.1093--1094; C.2.5--6, printed pp.144--145.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.ConstrainedSolvable
open ChapterC
variable {G : Type*} [Group G] [Finite G]

private theorem twoPerfect_le_of_index_le_two (B N : Subgroup G)
    (hB : IsPPerfect 2 B) (hi : N.index ≤ 2) : B ≤ N := by
  have hpos := N.index_ne_zero_of_finite
  have hc : N.index = 1 ∨ N.index = 2 := by omega
  rcases hc with h | h
  · rw [index_eq_one.mp h]; exact le_top
  · let : N.Normal := normal_of_index_eq_two h
    have hp : IsPGroup 2 (G ⧸ N) := IsPGroup.of_card (by
      change N.index = 2 ^ 1
      simpa only [pow_one] using h)
    have ht := hB.hom_eq_one_of_isPGroup hp ((QuotientGroup.mk' N).comp B.subtype)
    intro b hb
    exact (QuotientGroup.eq_one_iff b).mp (DFunLike.congr_fun ht ⟨b,hb⟩)

private theorem twoPerfect_normalizes_chi (X B : Subgroup G) [X.Normal]
    (hB : IsPPerfect 2 B)
    (hf : generalizedFitting X = pCore 2 X) (hr : primeRank 3 X ≤ 2)
    (K : Subgroup X) (hK : IsChiBlockIn K) :
    B ≤ normalizer (K.map X.subtype : Set G) := by
  classical
  let I := {Y : Subgroup X // IsChiBlockIn Y}
  let f : I → Subgroup G := fun i => i.val.map X.subtype
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact map_injective X.subtype_injective he
  have hsub : (Set.range fun g : G => (K.map X.subtype).map (MulAut.conj g).toMonoidHom) ⊆
      Set.range f := by
    rintro _ ⟨g,rfl⟩
    let e : X ≃* X := MulAut.conjNormal g
    refine ⟨⟨K.map e.toMonoidHom,RankOne.ChiProduct.chi_map_equiv e hK⟩,?_⟩
    change (K.map e.toMonoidHom).map X.subtype =
      (K.map X.subtype).map (MulAut.conj g).toMonoidHom
    rw [map_map,map_map]
    rfl
  have hi : (normalizer (K.map X.subtype : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans
      ((Set.ncard_range_of_injective hinj).le.trans
        (RankOne.ChiProduct.card_chiBlocks_le_two hf hr))
  exact twoPerfect_le_of_index_le_two B _ hB hi


private theorem twoPerfect_normalizes_chi_of_normalizes (D A : Subgroup G)
    (hA : IsPPerfect 2 A) (hn : A ≤ normalizer (D : Set G))
    (hf : generalizedFitting D = pCore 2 D) (hr : primeRank 3 D ≤ 2)
    (K : Subgroup D) (hK : IsChiBlockIn K) :
    A ≤ normalizer (K.map D.subtype : Set G) := by
  let H := D ⊔ A
  let D0 := D.subgroupOf H
  let A0 := A.subgroupOf H
  let e : D0 ≃* D := subgroupOfEquivOfLe le_sup_left
  let : D0.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hn)
  have hf0 : generalizedFitting D0 = pCore 2 D0 := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hf]
  have hr0 : primeRank 3 D0 ≤ 2 := (_root_.primeRank_le_of_injective 3 e.toMonoidHom e.injective).trans hr
  have ha0 : IsPPerfect 2 A0 := hA.of_surjective
    (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).symm.surjective
  have hh := twoPerfect_normalizes_chi D0 A0 ha0 hf0 hr0
    (K.map e.symm.toMonoidHom) (RankOne.ChiProduct.chi_map_equiv e.symm hK)
  have hm := (map_mono (f := H.subtype) hh).trans (le_normalizer_map H.subtype)
  rw [map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right)] at hm
  have he : ((K.map e.symm.toMonoidHom).map D0.subtype).map H.subtype = K.map D.subtype := by
    rw [map_map,map_map]
    rfl
  rwa [he] at hm

/-- A solvable characteristic-two subgroup normalized by M is controlled
when its Sylow is the marked two-subgroup and the original residual has
its normalizer in M. -/
theorem controlled_of_sylow
    {κ : GroupClass} (hG : IsSQTK κ G) (M D R : Subgroup G)
    (hn : M ≤ normalizer (D : Set G))
    (hRM : R ≤ M)
    (hs : Group.IsSolvable D) (hf : generalizedFitting D = pCore 2 D)
    (hSyl : ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = R)
    (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (hres : normalizer ((pResidual 2 M).map M.subtype : Set G) ≤ M) : D ≤ M := by
  obtain ⟨P,hP⟩ := hSyl
  have hRD : R ≤ D := hP ▸ map_subtype_le _
  have hp : (P : Subgroup D) = R.subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRD]
  have hc : (P : Subgroup D).characteristicNormalizerClosure ≤ M.subgroupOf D := by
    rw [hp]
    exact characteristicNormalizerClosure_subgroupOf_le hRD hcontrol
  obtain ⟨n,_,B,hB,hout,_,hprod⟩ := Section02Source.ordered_alternatingThree_product
    hs (hG.subgroup D) hf P (M.subgroupOf D) hc
  have hall (i : Fin n) : B i ≤ M.subgroupOf D := by
    let X := (B i).map D.subtype
    let Y := (pResidual 2 M).map M.subtype
    let e : B i ≃* X := equivMapOfInjective (B i) D.subtype D.subtype_injective
    have ha : IsAlternatingBlock X 3 := RankOne.Solvable.isAlternatingBlock_of_equiv e (hB i).2
    have hchi : IsChiBlockIn (B i) := ⟨(hB i).1,.inr ⟨3,by decide,(hB i).2⟩⟩
    have hnY := twoPerfect_normalizes_chi_of_normalizes D Y
      (isPPerfect_embedded_pResidual 2 M) ((map_subtype_le _).trans hn) hf
      ((_root_.primeRank_le_of_injective 3 D.subtype D.subtype_injective).trans
        (hG.stronglyQuasithin 3 Nat.prime_three (by decide))) (B i) hchi
    have hcard : Nat.card (X ⧸ pCore 2 X) = 3 := by
      obtain ⟨f⟩ := ha.2.2.quotient_iso
      rw [Nat.card_congr f.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      rfl
    have hXQ : X.pCoreIn 2 ≤ D.pCoreIn 2 := by
      rw [←map_pCoreIn_of_injective 2 (B i) D.subtype D.subtype_injective]
      exact map_mono (pCoreIn_le_of_subnormal 2 (hB i).1.subnormal)
    have hQM : D.pCoreIn 2 ≤ M := (pCoreIn_le_sylow D P).trans (hP ▸ hRM)
    have hcomm : ⁅X,Y⁆ ≤ D.pCoreIn 2 := by
      rw [commutator_comm]
      exact (commutator_le_pCoreIn_of_twoPerfect_of_normalizes_of_quotient_card_three
        X Y (isPPerfect_embedded_pResidual 2 M) hnY hcard).trans hXQ
    have hXM : X ≤ M :=
      (normalizes_residual_of_commutator_le_two X M M (D.pCoreIn 2)
        M.le_normalizer hQM (isPGroup_pCoreIn 2 D)
        ((map_subtype_le _).trans (D.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))) hcomm).trans hres
    exact map_le_iff_le_comap.mp hXM
  have hz : n = 0 := by
    by_contra hn0
    let i : Fin n := ⟨0,Nat.pos_of_ne_zero hn0⟩
    exact hout i (hall i)
  subst n
  intro d hd
  obtain ⟨m,b,he⟩ := hprod ⟨d,hd⟩
  have he' : (⟨d,hd⟩ : D) = m := by simpa using he
  change (⟨d,hd⟩ : D) ∈ M.subgroupOf D
  rw [he']
  exact m.property

/-- The normal-Sylow-two case of original 15.1.19(2), retaining relative
M-invariance and characteristic two only on K. -/
theorem controlled_of_odd_quotient
    {κ : GroupClass} (hG : IsSQTK κ G) (S : Sylow 2 G) (M K : Subgroup G)
    (hSM : (S : Subgroup G) ≤ M) (hn : M ≤ normalizer (K : Set G))
    (hf : generalizedFitting K = pCore 2 K)
    (ho : Odd (Nat.card (K ⧸ pCore 2 K)))
    (hcontrol : (M.pCoreIn 2).characteristicNormalizerClosure ≤ M)
    (hres : normalizer ((pResidual 2 M).map M.subtype : Set G) ≤ M) : K ≤ M := by
  let R := M.pCoreIn 2
  let Q := K.pCoreIn 2
  have hnQ : M ≤ normalizer (Q : Set G) := hn.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hQM : Q ≤ M := by
    let H := K ⊔ M
    have hQH : Q ≤ H := (pCoreIn_le 2 K).trans le_sup_left
    have hHQ : H ≤ normalizer (Q : Set G) := sup_le
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))) hnQ
    have hSH : (S : Subgroup G) ≤ H := hSM.trans le_sup_right
    have hcore := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) hQH hHQ
    have hP := pCoreIn_le_sylow H (S.subtype hSH)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSH] at hP
    exact (hcore.trans hP).trans hSM
  have hQR : Q ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) hQM hnQ
  let D := K ⊔ R
  have hRN : R ≤ normalizer (K : Set G) := (pCoreIn_le 2 M).trans hn
  have hsyl : ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = R := by
    apply IsPGroup.exists_sylow_sup_of_coprime_index K R (isPGroup_pCoreIn 2 M)
      hRN (pCore 2 K) _ hQR
    exact fun hd => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)
  have hfD : generalizedFitting D = pCore 2 D :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (centralizer_pCore_sup_le 2 K R ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
        (isPGroup_pCoreIn 2 M) hRN)
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (K ⧸ pCore 2 K) := _root_.odd_order_theorem _ ho
  let : Group.IsSolvable K := (Group.isSolvable_iff_subgroup_quotient (pCore 2 K)).mpr
    ⟨inferInstance,inferInstance⟩
  let : Group.IsNilpotent R := (isPGroup_pCoreIn 2 M).isNilpotent
  have hsD : Group.IsSolvable D := Group.isSolvable_sup_of_normalizes K R hRN
  have hnD : M ≤ normalizer (D : Set G) :=
    (le_inf hn (M.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))).trans
        (normalizer_inf_normalizer_le_normalizer_sup K R)
  exact le_sup_left.trans (controlled_of_sylow hG M D R hnD (pCoreIn_le 2 M)
    hsD hfD hsyl hcontrol hres)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.ConstrainedSolvable


namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Original 15.1.19(2), in the exact fixed centralizer and marked subgroup.
The odd quotient is the literal condition K=O₂,₂′(K). -/
theorem constrained_solvable_control (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hSyl : Chapter1.IsSylowIn 2 d.S d.G1)
    (hcontrol : d.Q1.characteristicNormalizerClosure ≤ Mc)
    (hTn : (T : Subgroup G) ≤ normalizer (d.MZ : Set G))
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hn : d.MZ ≤ normalizer (K : Set G))
    (hf : generalizedFitting K = pCore 2 K)
    (ho : Odd (Nat.card (K ⧸ pCore 2 K))) : K ≤ d.MZ := by
  let := h.elementary
  let H := d.G1
  let N := d.MZ.subgroupOf H
  let B := K.subgroupOf H
  let e : B ≃* K := subgroupOfEquivOfLe hK
  obtain ⟨P,hP⟩ := hSyl
  have hSM : (P : Subgroup H) ≤ N := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    have hs : (x : G) ∈ d.S := hP ▸ mem_map_of_mem H.subtype hx
    exact ⟨x.property,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hs)).symm)⟩
  have hnB : N ≤ normalizer (B : Set H) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hn hx) b
  have hfB : generalizedFitting B = pCore 2 B := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hf]
  have hoB : Odd (Nat.card (B ⧸ pCore 2 B)) := by
    rwa [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
  have hc : (N.pCoreIn 2).characteristicNormalizerClosure ≤ N := by
    rw [show N = d.MZ.subgroupOf H from rfl,pCoreIn_subgroupOf 2 d.MZ H inf_le_left]
    exact caseI_intrinsic_characteristic_control H Mc d.Q1
      (d.Q1_le_MZ.trans inf_le_left) hcontrol
  have hbound := CaseIMarkedSubgroup.residual_normalizer_control hG d.Z1_le_fixed
    d.Z1_ne_bot d.M_eq_centralizer_sup_sylow hM hu hne h hmany hres hTn ⟨P,hP⟩
  have hY : ((pResidual 2 N).map N.subtype).map H.subtype =
      (pResidual 2 d.MZ).map d.MZ.subtype := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le (show d.MZ ≤ H from inf_le_left)]
  have hr : normalizer ((pResidual 2 N).map N.subtype : Set H) ≤ N := by
    intro x hx
    refine ⟨x.property,hbound ?_⟩
    have hm := le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx)
    rwa [hY] at hm
  have hle := ConstrainedSolvable.controlled_of_odd_quotient
    (caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
      ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)))
    P N B hSM hnB hfB hoB hc hr
  intro k hk
  exact hle (show (⟨k,hK hk⟩ : H) ∈ B from hk)

/-- The original-marker application requires no exchanged selection. -/
theorem PreExclusionSource.constrained_solvable_control
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hn : d.MZ ≤ normalizer (K : Set G))
    (hf : generalizedFitting K = pCore 2 K)
    (ho : Odd (Nat.card (K ⧸ pCore 2 K))) : K ≤ d.MZ :=
  d.constrained_solvable_control hG hM hu hne h hmany hres s.centralizer_sylow
    s.characteristic_control s.sylow_normalizes_MZ hK hn hf ho

/-- The later exchanged application retains both source plane sizes. -/
theorem ExchangedSource.constrained_solvable_control
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hn : d.MZ ≤ normalizer (K : Set G))
    (hf : generalizedFitting K = pCore 2 K)
    (ho : Odd (Nat.card (K ⧸ pCore 2 K))) : K ≤ d.MZ :=
  d.constrained_solvable_control hG hM hu hne h hmany hres s.centralizer_sylow
    s.characteristic_control s.sylow_normalizes_MZ hK hn hf ho


/-- The literal lower mixed-core condition in 15.1.19(2) has odd quotient
above the two-core. -/
private theorem odd_quotient_of_mixed_core (A : Type*) [Group A] [Finite A]
    (hm : (pPrimeCore 2 (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A)) = ⊤) :
    Odd (Nat.card (A ⧸ pCore 2 A)) := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have ht : pPrimeCore 2 (A ⧸ pCore 2 A) = ⊤ := by
    have hh := congrArg (Subgroup.map q) hm
    simpa only [q,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using hh
  have hc := pPrimeCore_coprime_card (p := 2) (G := A ⧸ pCore 2 A)
  rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
  exact Nat.not_even_iff_odd.mp (fun he =>
    Nat.prime_two.coprime_iff_not_dvd.mp hc (even_iff_two_dvd.mp he))

/-- Original 15.1.19(2) with the literal O₂,₂′ preimage, for every invariant
subgroup of the fixed G₁, before exchanged selection. -/
theorem PreExclusionSource.constrained_mixed_core_control
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hn : d.MZ ≤ normalizer (K : Set G))
    (hf : generalizedFitting K = pCore 2 K)
    (hm : (pPrimeCore 2 (K ⧸ pCore 2 K)).comap (QuotientGroup.mk' (pCore 2 K)) = ⊤) :
    K ≤ d.MZ :=
  s.constrained_solvable_control (h := h) hG hM hu hne hmany hres hK hn hf
    (odd_quotient_of_mixed_core K hm)


end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
