module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.SolvableSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.FiveModule
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.Alternating.Aut
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.SymmetricFive.FourNormalizedResidual

/-!
# The direct A₅ residual argument in 13.6.26(2)

Let Y = O^{p′}(O_{2,p}(H)) for p > 3. The literal quotient-preimage
construction of O_{2,p}(H) makes its order, and hence Y's order, prime to
three. The solvable-overgroup theorem places Y in M = N_G(L). The original
conjugation action on L/O₂(L) ≃ A₅ maps T ∩ L onto a full Sylow four-group.
Since Y is two-perfect, its three-free image in S₅ is trivial by the
four-group normalization lemma.

Thus [Y,L] ≤ O₂(L). Inside Y O₂(L), Y is the two-residual, so L normalizes
Y. If Y were nontrivial, characteristic two supplies its nontrivial
two-core. Both L and T normalize that core, and uniqueness of the maximal
two-local over LT places its normalizer in M. This contradicts H outside M.
The residual vanishes and the original iterated-core equality follows.

The final consumer retains the genuine earlier A₅ setup and ambient QTKE
hypotheses. Its local module parameter and solvable-overgroup premises are
discharged; it uses neither Group.IsPerfect Y nor Earlier1338Two.

Source: Aschbacher–Smith, 13.6.26(2), printed p.934, specializing the
normalizer argument of 13.3.8 to the actual A₅ quotient.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
open Subgroup Theory.GroupTheory
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G]

private abbrev A5 := alternatingGroup (Fin 5)
private abbrev S5 := Equiv.Perm (Fin 5)
private def autFive : S5 ≃* MulAut A5 :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))

private def fiveActor (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* A5) :
    normalizer (L : Set G) →* S5 :=
  autFive.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp
      ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom))

omit [Finite G] in
private theorem fiveActor_on_L (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* A5) (l : L) :
    fiveActor L e ⟨l.val, L.le_normalizer l.property⟩ =
      (e (QuotientGroup.mk' (pCore 2 L) l)).val := by
  have hq : quotientAut (pCore 2 L)
      (L.normalizerMonoidHom ⟨l.val, L.le_normalizer l.property⟩) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 L) l) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore 2 L) (l * a * l⁻¹) = _
    simp only [map_mul, map_inv, MulAut.conj_apply]
  apply autFive.injective
  change autFive (autFive.symm ((MulAut.congr e)
    (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom ⟨l.val, L.le_normalizer l.property⟩)))) = _
  rw [autFive.apply_symm_apply, hq]
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change (e ((QuotientGroup.mk' (pCore 2 L) l) * e.symm a *
    (QuotientGroup.mk' (pCore 2 L) l)⁻¹)).val = _
  simp only [map_mul, map_inv, e.apply_symm_apply]
  rfl

omit [Finite G] in
private theorem fiveActor_trivial_commutator (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* A5) (n : normalizer (L : Set G))
    (hn : fiveActor L e n = 1) (l : L) : ⁅n.val, l.val⁆ ∈ L.pCoreIn 2 := by
  have ha : quotientAut (pCore 2 L) (L.normalizerMonoidHom n) = 1 := by
    apply (MulAut.congr e).injective
    apply autFive.symm.injective
    simpa only [fiveActor, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_one] using hn
  have he := congrArg (fun a : MulAut (L ⧸ pCore 2 L) =>
    a (QuotientGroup.mk' (pCore 2 L) l)) ha
  rw [quotientAut_apply_mk] at he
  have hk : L.normalizerMonoidHom n l * l⁻¹ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom n l * l⁻¹) = 1
    rw [map_mul, map_inv, he]
    exact mul_inv_cancel _
  exact mem_map.mpr ⟨_, hk, rfl⟩

omit [Finite G] in
private theorem core_le_sylow_of_normalized (T : Sylow 2 G) (L : Subgroup G)
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G)) : L.pCoreIn 2 ≤ (T : Subgroup G) := by
  let N := normalizer (L : Set G)
  have hQN : L.pCoreIn 2 ≤ N := (map_subtype_le _).trans L.le_normalizer
  have hNQ : N ≤ normalizer (L.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hQQ : L.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L) hQN hNQ
  have hNT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hc := pCoreIn_le_sylow N (T.subtype hTN)
    rw [Sylow.coe_subtype] at hc
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hc hx
    exact ht
  exact hQQ.trans hNT

private theorem normalizer_le_from_unique
    (T : Sylow 2 G) (L M : Subgroup G)
    (hu : maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) = {M})
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hN : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G)) :
    normalizer (Q : Set G) ≤ M := by
  obtain ⟨N, hNN, hmax⟩ := Finite.exists_le_maximal
    (show IsTwoLocal (normalizer (Q : Set G)) from ⟨Q, hne, hQ, rfl⟩)
  have hm : N ∈ maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) :=
    ⟨hmax, hN.trans hNN⟩
  have he : N = M := Set.mem_singleton_iff.mp (hu ▸ hm)
  exact hNN.trans_eq he

omit [Finite G] in
private theorem normal_perfect_kernel_normalized
    (T : Sylow 2 G) (L H Y : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    (hQ : L.pCoreIn 2 ≤ (T : Subgroup G)) (hp : IsPPerfect 2 Y)
    (hc : ⁅Y, L⁆ ≤ L.pCoreIn 2) : L ≤ normalizer (Y : Set G) := by
  let Q := L.pCoreIn 2
  let B := Y ⊔ Q
  have hLQ : L ≤ normalizer (Q : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hLB : L ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl x hx
    have hm : B.map (MulAut.conj l).toMonoidHom ≤ B := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        have hc' : ⁅l, y⁆ ∈ Q := by
          rw [commutator_comm] at hc
          exact hc (commutator_mem_commutator hl hy)
        have hh := B.mul_mem (mem_sup_right hc') (mem_sup_left hy)
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one,
          MulAut.conj_apply, MulEquiv.coe_toMonoidHom] using hh
      · rintro _ ⟨q, hq, rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp (hLQ hl) q).mp hq)
    exact hm (mem_map_of_mem _ hx)
  let : (Y.subgroupOf B).Normal :=
    normal_subgroupOf_of_le_normalizer
      (sup_le Y.le_normalizer ((hQ.trans hTH).trans hHY))
  have hp' : IsPPerfect 2 (Y.subgroupOf B) :=
    hp.of_surjective (subgroupOfEquivOfLe (show Y ≤ B from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show Y ≤ B from le_sup_left)).symm.surjective
  have hs : Y.subgroupOf B ⊔ Q.subgroupOf B = ⊤ := by
    rw [← subgroupOf_sup (show Y ≤ B from le_sup_left) (show Q ≤ B from le_sup_right)]
    exact subgroupOf_self B
  have he : (pResidual 2 B).map B.subtype = Y := by
    rw [pResidual_eq_of_isPPerfect_sup (Y.subgroupOf B) (Q.subgroupOf B)
      hp' (isPGroup_pCoreIn 2 L).comap_subtype hs,
      map_subgroupOf_eq_of_le (show Y ≤ B from le_sup_left)]
  rw [← he]
  exact hLB.trans (normalizer_le_normalizer_characteristic_image B (pResidual 2 B))


private theorem fiveActor_image_eq_bot (T : Sylow 2 G) (L Y : Subgroup G)
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hYN : Y ≤ normalizer (L : Set G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (e : (L ⧸ pCore 2 L) ≃* A5) (hp : IsPPerfect 2 Y)
    (h3 : ¬ 3 ∣ Nat.card Y) :
    (Y.subgroupOf (normalizer (L : Set G))).map (fiveActor L e) = ⊥ := by
  let N := normalizer (L : Set G)
  let D := L.subgroupOf N
  let S := T.subtype hTN
  let Yn := Y.subgroupOf N
  let θ := fiveActor L e
  let : D.Normal := (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal D
  let f : D →* A5 := (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).comp
    (subgroupOfEquivOfLe L.le_normalizer).toMonoidHom
  have hf : Function.Surjective f := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe L.le_normalizer).surjective)
  have hp' : IsPPerfect 2 Yn := hp.of_surjective
    (subgroupOfEquivOfLe hYN).symm.toMonoidHom (subgroupOfEquivOfLe hYN).symm.surjective
  apply SymmetricFive.twoPerfect_eq_bot_of_three_free_normalized_sylow
    (P.mapSurjective hf) (Yn.map θ)
  · change ((P : Subgroup D).map f).map (alternatingGroup (Fin 5)).subtype ≤ _
    rintro _ ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    have hxT : x.val.val ∈ (T : Subgroup G) := by
      rw [hP] at hx
      exact hx
    have hxN : x.val ∈ normalizer (Yn : Set N) := by
      apply Y.le_normalizer_comap N.subtype
      exact hTY hxT
    have hh := Yn.le_normalizer_map θ (mem_map_of_mem θ hxN)
    have he : θ x.val = (f x).val := fiveActor_on_L L e
      ((subgroupOfEquivOfLe L.le_normalizer) x)
    rw [he] at hh
    exact hh
  · exact hp'.of_surjective (θ.subgroupMap Yn) (θ.subgroupMap_surjective Yn)
  · intro hd
    apply h3
    have hd' := hd.trans (card_map_dvd (H := Yn) θ)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hYN).toEquiv] at hd'


/-- A three-free two-perfect subgroup normal in the original outside overgroup
cannot be contained in the normalizer of the marked A₅ component. -/
theorem three_free_twoPerfect_normal_subgroup_eq_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (L M H Y : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hM : M = normalizer (L : Set G))
    (hu : maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hYH : Y ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    (hp : IsPPerfect 2 Y) (hYM : Y ≤ M) (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  by_contra hYne
  let N := normalizer (L : Set G)
  let θ := fiveActor L e
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans
    (show L ⊔ (T : Subgroup G) ≤ M from
      (show M ∈ maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) from
        hu.symm ▸ Set.mem_singleton M).2)
  have hTN : (T : Subgroup G) ≤ N := hTM.trans_eq hM
  have hYN : Y ≤ N := hYM.trans_eq hM
  have hQT := core_le_sylow_of_normalized T L hTN
  have hzero := fiveActor_image_eq_bot T L Y hTN hYN (hH.1.2.trans hHY) e hp h3
  have hc : ⁅Y, L⁆ ≤ L.pCoreIn 2 := by
    apply commutator_le.mpr
    intro y hy l hl
    apply fiveActor_trivial_commutator L e ⟨y, hYN hy⟩ _ ⟨l, hl⟩
    have hm : θ ⟨y, hYN hy⟩ ∈ (Y.subgroupOf N).map θ := mem_map_of_mem θ hy
    rw [hzero] at hm
    exact hm
  have hLY := normal_perfect_kernel_normalized T L H Y hH.1.2 hHY hQT hp hc
  have hHe : H ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1
  have hYNH : (Y.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYH).mpr hHY
  have hYe : Y ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_3_1 hHe hYne hYH hYNH.isSubnormal
  have hcore : Y.pCoreIn 2 ≠ ⊥ := by
    intro hz
    change Y ⊓ centralizer (Y.pCoreIn 2 : Set G) ≤ Y.pCoreIn 2 at hYe
    have hc : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)
    rw [hz, hc, inf_top_eq] at hYe
    exact hYne (bot_unique hYe)
  have hNC : normalizer (Y : Set G) ≤ normalizer (Y.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
  exact hH.2 ((hHY.trans hNC).trans (normalizer_le_from_unique T L M hu _
    (isPGroup_pCoreIn 2 Y) hcore
    ((sup_le hLY (hH.1.2.trans hHY)).trans hNC)))

/-- The literal iterated core has order prime to three for p > 3. -/
theorem O2p_not_three_dvd_card (H : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) : ¬ 3 ∣ Nat.card (O2p H p) := by
  let D := twoPCore p H
  let q := QuotientGroup.mk' (pCore 2 H)
  let f : D →* (H ⧸ pCore 2 H) := q.comp D.subtype
  have hk : f.ker = (pCore 2 H).subgroupOf D := by
    ext x
    change q x.val = 1 ↔ x.val ∈ pCore 2 H
    exact QuotientGroup.eq_one_iff _
  have hker : IsPGroup 2 f.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_subtype
  have hle : f.range ≤ pCore p (H ⧸ pCore 2 H) := by
    rintro _ ⟨x, rfl⟩
    exact x.property
  have hrange : IsPGroup p f.range := pCore_isPGroup.of_injective
    (inclusion hle) (inclusion_injective hle)
  obtain ⟨a, ha⟩ := hker.exists_card_eq
  obtain ⟨b, hb⟩ := hrange.exists_card_eq
  have hc := f.ker.card_mul_index
  rw [index_ker, ha, hb] at hc
  have h3D : ¬ 3 ∣ Nat.card D := by
    rw [← hc]
    intro hd
    rcases Nat.prime_three.dvd_mul.mp hd with hd | hd
    · have hh := Nat.prime_three.dvd_of_dvd_pow hd
      norm_num at hh
    · have hh := (Nat.dvd_prime (Fact.out : p.Prime)).mp
        (Nat.prime_three.dvd_of_dvd_pow hd)
      omega
  rwa [show Nat.card (O2p H p) = Nat.card D from
    (card_map_of_injective H.subtype_injective)]

/-- The source prime-to-p residual inherits the iterated core's three-free order. -/
theorem O2pResidual_not_three_dvd_card (H : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) : ¬ 3 ∣ Nat.card (O2pResidual H p) := by
  intro hd
  exact O2p_not_three_dvd_card H p hp (hd.trans (card_dvd_of_le (O2pResidual_le H p)))

/-- The actual residual vanishes in the original A₅ source setup, with the
solvable-overgroup and local module-parameter premises discharged. -/
theorem O2pResidual_eq_bot_of_A5_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV) (L₁ G₁ : Subgroup G)
    {H : Subgroup G} (hH : H ∈ Chapter13.Section08.Source.Hz L₁ T G₁ M)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) : O2pResidual H p = ⊥ := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have h25 := s.solvable_HOver_le_source
    (s.coordinates.localA_eq_one s.alternating_le_actor)
  exact three_free_twoPerfect_normal_subgroup_eq_bot hG T L M H (O2pResidual H p)
    s.quotient s.local_normalizer s.unique_overgroup ⟨⟨hH.1.1, hTH⟩, hH.2.2⟩
    ((O2pResidual_le H p).trans (O2p_le H p)) (le_normalizer_O2pResidual H p)
    (O2pResidual_isTwoPerfect H p hp)
    (O2pResidual_le_M_of_solvable_HOver H M T hH.1.1 hTH h25 p)
    (O2pResidual_not_three_dvd_card H p hp)

/-- Original 13.6.26(2) from the marked A₅ setup and ambient simple QTKE
hypotheses. The universal earlier 13.3.8(2) implication is unnecessary. -/
theorem source_13_6_26_2_of_A5_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV) (L₁ G₁ : Subgroup G)
    {H : Subgroup G} (hH : H ∈ Chapter13.Section08.Source.Hz L₁ T G₁ M)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) : O2p H p = Chapter13.Section08.Source.QH H :=
  O2p_eq_QH_of_residual_eq_bot H p hp (O2pResidual_eq_bot_of_A5_setup hG s L₁ G₁ hH p hp)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
