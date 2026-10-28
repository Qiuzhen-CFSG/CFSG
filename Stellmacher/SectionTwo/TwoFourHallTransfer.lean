module

public import Stellmacher.SectionsOneToFourDefs
public import Stellmacher.SectionOne.InvolutionPGroupSmallIndexClassification
public import Stellmacher.TwoResidualSylowSupplement
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.Hall.Existence
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The Hall transfer at the end of Stellmacher (2.4)

This module proves the final local-to-global step in Stellmacher (2.4),
Journal of Algebra 190 (1997), p. 20.  Let `L₁ ≤ L` be the local
subgroup supplied earlier in the proof, and suppose the same ambient subgroup
`B` is the image of Sylow 2-subgroups of both `L` and `L₁`.  A bound on
`[O₂(L₁), O²(L₁)]` then implies the required ambient bound on
`[O₂(G), O²(G)]` when `L₁` and the ambient Sylow subgroup generate `G`.

The proof follows the source's Hall-subgroup argument.  Write `O` for the
ambient image of `O₂(L)`.  Sylow control gives `O ≤ B ≤ L₁`, so the
local hypothesis makes `O²(L₁)` centralize `O/V`.  Its centralizer preimage
inside `L` is a normal subgroup `C` with `C ∨ S = G`.  A Hall `2'`-subgroup
`T` of the solvable group `C` complements `S ∩ C`, hence `T ∨ S = G`.
The commutator `[O₂(G),T]` lies in `O`; centralization modulo `V` and the
coprime identity `[[O₂(G),T],T] = [O₂(G),T]` put it in `V`.  Finally, a
normal-closure quotient transfers this bound from `T` to `O²(G)`.

In particular, the argument does not assume the generally unavailable
containment `O₂(G) ≤ L₁`.
-/

namespace Stellmacher.SectionTwo

universe u

private theorem complementary_hall_sup_eq_top
    {G : Type*} [Group G] [Finite G]
    {pi : Set Nat.Primes} {Hpi Hpi' : Subgroup G}
    (hHpi : IsHallSubgroup pi Hpi)
    (hHpi' : IsHallSubgroup {p | p ∉ pi} Hpi') :
    Hpi' ⊔ Hpi = ⊤ := by
  have hcop_cards : Nat.Coprime (Nat.card Hpi') (Nat.card Hpi) := by
    refine Nat.coprime_of_dvd ?_
    intro p hp_prime hp_dvd_Hpi' hp_dvd_Hpi
    have hp_not_mem : (⟨p, hp_prime⟩ : Nat.Primes) ∉ pi :=
      hHpi'.p_in_pi_of_p_dvd_card ⟨p, hp_prime⟩ hp_dvd_Hpi'
    have hp_mem : (⟨p, hp_prime⟩ : Nat.Primes) ∈ pi :=
      hHpi.p_in_pi_of_p_dvd_card ⟨p, hp_prime⟩ hp_dvd_Hpi
    exact (hp_not_mem hp_mem).elim
  have hcop_indices : Nat.Coprime Hpi.index Hpi'.index := by
    refine Nat.coprime_of_dvd ?_
    intro p hp_prime hp_dvd_Hpiidx hp_dvd_Hpi'idx
    have hp_not_mem : (⟨p, hp_prime⟩ : Nat.Primes) ∉ pi :=
      hHpi.p_in_pi_of_p_dvd_index ⟨p, hp_prime⟩ hp_dvd_Hpiidx
    have hp_mem : (⟨p, hp_prime⟩ : Nat.Primes) ∈ pi := by
      have hnot_not_mem :=
        hHpi'.p_in_pi_of_p_dvd_index ⟨p, hp_prime⟩ hp_dvd_Hpi'idx
      change ¬ ((⟨p, hp_prime⟩ : Nat.Primes) ∉ pi) at hnot_not_mem
      exact Classical.not_not.mp hnot_not_mem
    exact (hp_not_mem hp_mem).elim
  have hcard_dvd_index : Nat.card Hpi' ∣ Hpi.index := by
    have hcard_dvd_G : Nat.card Hpi' ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card Hpi'
    have hcard_dvd_mul : Nat.card Hpi' ∣ Hpi.index * Nat.card Hpi := by
      simpa [Subgroup.index_mul_card] using hcard_dvd_G
    exact hcop_cards.dvd_of_dvd_mul_right hcard_dvd_mul
  have hindex_dvd_card : Hpi.index ∣ Nat.card Hpi' := by
    have hindex_dvd_G : Hpi.index ∣ Nat.card G :=
      Subgroup.index_dvd_card (H := Hpi)
    have hindex_dvd_mul : Hpi.index ∣ Nat.card Hpi' * Hpi'.index := by
      simpa [Subgroup.card_mul_index] using hindex_dvd_G
    exact hcop_indices.dvd_of_dvd_mul_right hindex_dvd_mul
  have hcard_eq_index : Nat.card Hpi' = Hpi.index :=
    Nat.dvd_antisymm hcard_dvd_index hindex_dvd_card
  have hcard_mul : Nat.card Hpi' * Nat.card Hpi = Nat.card G := by
    calc
      Nat.card Hpi' * Nat.card Hpi = Hpi.index * Nat.card Hpi := by
        rw [hcard_eq_index]
      _ = Nat.card G := Subgroup.index_mul_card (H := Hpi)
  exact (Subgroup.isComplement'_of_coprime hcard_mul hcop_cards).sup_eq_top

private theorem normal_pSubgroup_le_core_ambient
    {G : Type*} [Group G] {p : ℕ}
    (Q K : Subgroup G) (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQnormal : (Q.subgroupOf K).Normal) :
    Q ≤ (pCore p K).map K.subtype := by
  have hQpK : IsPGroup p (Q.subgroupOf K) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hle : Q.subgroupOf K ≤ pCore p K :=
    le_sSup ⟨hQnormal, hQpK⟩
  calc
    Q = (Q.subgroupOf K).map K.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQK).symm
    _ ≤ (pCore p K).map K.subtype := Subgroup.map_mono hle

private theorem residual_transfer_of_sup_sylow
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (V T : Subgroup G) [V.Normal]
    (hgen : T ⊔ (S : Subgroup G) = ⊤)
    (hcomm : ⁅pCore 2 G, T⁆ ≤ V) :
    ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ V := by
  classical
  let N := Subgroup.normalClosure (T : Set G)
  have hNnormal : N.Normal := by
    dsimp only [N]
    infer_instance
  let _ : N.Normal := hNnormal
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hTN : T ≤ N := Subgroup.le_normalClosure
  have hTmap : T.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q, QuotientGroup.ker_mk'] using hTN
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  have htopmap : (⊤ : Subgroup G).map q = ⊤ := by
    simpa only [MonoidHom.range_eq_map] using q.range_eq_top_of_surjective hqsurj
  have hSmap : (S : Subgroup G).map q = ⊤ := by
    have hmapped := congrArg (fun K : Subgroup G => K.map q) hgen
    rw [Subgroup.map_sup, hTmap, bot_sup_eq, htopmap] at hmapped
    exact hmapped
  have hquotientTwo : IsPGroup 2 (G ⧸ N) := by
    have hP : IsPGroup 2 ((S : Subgroup G).map q) := S.isPGroup'.map q
    rw [hSmap] at hP
    exact hP.of_equiv Subgroup.topEquiv
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hquotientTwo
  let topSubtype : (⊤ : Subgroup G) →* G := (⊤ : Subgroup G).subtype
  let Ntop : Subgroup (⊤ : Subgroup G) := N.comap topSubtype
  have htopSurj : Function.Surjective topSubtype := by
    intro g
    exact ⟨⟨g, trivial⟩, rfl⟩
  have hNtopNormal : Ntop.Normal := by
    exact Subgroup.Normal.comap (show N.Normal from inferInstance) topSubtype
  have hNtopIndex : Ntop.index = 2 ^ n := by
    calc
      Ntop.index = N.index := Subgroup.index_comap_of_surjective N htopSurj
      _ = Nat.card (G ⧸ N) := Subgroup.index_eq_card N
      _ = 2 ^ n := hn
  have hresNtop : twoResidualSubgroup (⊤ : Subgroup G) ≤ Ntop := by
    apply sInf_le
    exact ⟨hNtopNormal, n, hNtopIndex⟩
  have hresN : twoResidualAmbient (⊤ : Subgroup G) ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hresNtop hx
  have hQN : ⁅pCore 2 G, N⁆ ≤ V :=
    Subgroup.commutator_normalClosure_le_of_normal (pCore 2 G) T V hcomm
  exact (Subgroup.commutator_mono le_rfl hresN).trans hQN

/-- The mapped local residual bound in Stellmacher (2.4) transfers to the
ambient residual bound. -/
public theorem two_four_hall_residual_transfer
    {G : Type u} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G)
    (S : Sylow 2 G) (V L L₁ B : Subgroup G)
    (hVnormal : V.Normal) (hLnormal : L.Normal)
    (hVelem : IsElementaryAbelian 2 V)
    (hVL : V ≤ L) (hBS : B ≤ (S : Subgroup G))
    (PL : Sylow 2 L) (hPLmap : PL.map L.subtype = B)
    (P₁ : Sylow 2 L₁) (hP₁map : P₁.map L₁.subtype = B)
    (hL₁L : L₁ ≤ L)
    (hgen : L₁ ⊔ (S : Subgroup G) = ⊤)
    (hlocal :
      (⁅pCore 2 L₁, twoResidualAmbient (⊤ : Subgroup L₁)⁆).map
        L₁.subtype ≤ V) :
    ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ V := by
  classical
  let _ : V.Normal := hVnormal
  let _ : L.Normal := hLnormal
  let _ : IsElementaryAbelian 2 V := hVelem
  let Q := pCore 2 G
  let O := (pCore 2 L).map L.subtype
  have hOnormal : O.Normal := by
    dsimp only [O]
    exact ConjAct.normal_of_characteristic_of_normal
  let _ : O.Normal := hOnormal
  have hOtwo : IsPGroup 2 O := by
    exact (pCore_isPGroup (p := 2) (G := L)).map L.subtype
  have hOleB : O ≤ B := by
    rw [← hPLmap]
    exact Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal PL)
  have hBleL₁ : B ≤ L₁ := by
    rw [← hP₁map]
    exact Subgroup.map_subtype_le (P₁ : Subgroup L₁)
  have hOleL₁ : O ≤ L₁ := hOleB.trans hBleL₁
  have hOsubNormal : (O.subgroupOf L₁).Normal :=
    (show O.Normal from inferInstance).subgroupOf L₁
  have hOleCoreL₁ : O ≤ (pCore 2 L₁).map L₁.subtype :=
    normal_pSubgroup_le_core_ambient O L₁ hOleL₁ hOtwo hOsubNormal
  have hVtwo : IsPGroup 2 V := by
    exact IsElementaryAbelian.isPGroup 2 V
  have hVsubNormal : (V.subgroupOf L).Normal :=
    (show V.Normal from inferInstance).subgroupOf L
  have _hVleO : V ≤ O :=
    normal_pSubgroup_le_core_ambient V L hVL hVtwo hVsubNormal
  let R := (twoResidualAmbient (⊤ : Subgroup L₁)).map L₁.subtype
  have hOR : ⁅O, R⁆ ≤ V := by
    have hmono :
        ⁅O, R⁆ ≤ ⁅(pCore 2 L₁).map L₁.subtype, R⁆ :=
      Subgroup.commutator_mono hOleCoreL₁ le_rfl
    have hlocal' := hlocal
    rw [Subgroup.map_commutator] at hlocal'
    exact hmono.trans hlocal'
  let qV : G →* G ⧸ V := QuotientGroup.mk' V
  let Obar : Subgroup (G ⧸ V) := O.map qV
  have hObarNormal : Obar.Normal := by
    dsimp only [Obar]
    exact Subgroup.Normal.map (show O.Normal from inferInstance) qV
      (QuotientGroup.mk'_surjective V)
  let _ : Obar.Normal := hObarNormal
  let C : Subgroup G :=
    L ⊓ (Subgroup.centralizer (Obar : Set (G ⧸ V))).comap qV
  have hCnormal : C.Normal := by
    dsimp only [C]
    infer_instance
  let _ : C.Normal := hCnormal
  have hRleC : R ≤ C := by
    refine le_inf (show R ≤ L from ?_) ?_
    · exact (Subgroup.map_subtype_le _).trans hL₁L
    · apply Subgroup.map_le_iff_le_comap.mp
      apply Subgroup.le_centralizer_iff.mp
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      rw [← Subgroup.map_commutator]
      apply (Subgroup.map_eq_bot_iff _).mpr
      simpa only [qV, QuotientGroup.ker_mk', Obar] using hOR
  have hlocalGen : R ⊔ B = L₁ := by
    have hmapped := congrArg (fun K : Subgroup L₁ => K.map L₁.subtype)
      (Stellmacher.twoResidualAmbient_top_sup_sylow P₁)
    rw [Subgroup.map_sup, hP₁map,
      show (⊤ : Subgroup L₁).map L₁.subtype = L₁ by
        exact (MonoidHom.range_eq_map L₁.subtype).symm.trans
          (Subgroup.range_subtype L₁)] at hmapped
    exact hmapped
  have hL₁CS : L₁ ≤ C ⊔ (S : Subgroup G) := by
    rw [← hlocalGen]
    exact sup_le (hRleC.trans le_sup_left) (hBS.trans le_sup_right)
  have hgenC : C ⊔ (S : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le hL₁CS le_sup_right
  let pi : Set Nat.Primes := {p | p.val = 2}
  have hsolvC : Group.IsSolvable C := by
    let _ : Group.IsSolvable G := hsolv
    infer_instance
  let _ : MulDistribMulAction Unit C := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  obtain ⟨T, hTHall, _hTinv⟩ := exists_isHallSubgroup_isInvariant
    (G := C) (A := Unit) hsolvC (by simp) {p | p ∉ pi}
  obtain ⟨U, hUeq⟩ := S.exists_subgroupOf_eq_of_normal C
  have hUHall : IsHallSubgroup pi (U : Subgroup C) := by
    refine isHallSubgroup_of _ _ ?_ ?_
    · intro q hq
      obtain ⟨n, hn⟩ := U.isPGroup'.exists_card_eq
      exact Nat.prime_eq_prime_of_dvd_pow q.property Nat.prime_two
        (by simpa [hn] using hq)
    · intro q hq hqdvd
      have hqeq : q.val = 2 := hq
      exact U.not_dvd_index (by simpa [hqeq] using hqdvd)
  have hTU : T ⊔ (U : Subgroup C) = ⊤ :=
    complementary_hall_sup_eq_top hUHall hTHall
  let T₀ : Subgroup G := T.map C.subtype
  have hTC : T₀ ≤ C := Subgroup.map_subtype_le T
  have hUC : (U : Subgroup C).map C.subtype = (S : Subgroup G) ⊓ C := by
    rw [hUeq, Subgroup.subgroupOf_map_subtype]
  have hCgen : C ≤ T₀ ⊔ (S : Subgroup G) := by
    have hmapped := congrArg (fun K : Subgroup C => K.map C.subtype) hTU
    rw [Subgroup.map_sup, hUC,
      show (⊤ : Subgroup C).map C.subtype = C by
        exact (MonoidHom.range_eq_map C.subtype).symm.trans
          (Subgroup.range_subtype C)] at hmapped
    rw [← hmapped]
    exact sup_le le_sup_left (inf_le_left.trans le_sup_right)
  have hgenT : T₀ ⊔ (S : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← hgenC]
    exact sup_le hCgen le_sup_right
  have hOT : ⁅O, T₀⁆ ≤ V := by
    have hTmap :
        T₀.map qV ≤ Subgroup.centralizer (Obar : Set (G ⧸ V)) := by
      apply Subgroup.map_le_iff_le_comap.mpr
      exact hTC.trans inf_le_right
    have hzero : (⁅O, T₀⁆).map qV = ⊥ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mp hTmap)
    have hker := (Subgroup.map_eq_bot_iff _).mp hzero
    simpa only [qV, QuotientGroup.ker_mk'] using hker
  have hQTleO : ⁅Q, T₀⁆ ≤ O := by
    have hQTleQL : ⁅Q, T₀⁆ ≤ Q ⊓ L := by
      apply le_inf
      · exact Subgroup.commutator_le_left Q T₀
      · exact ((Subgroup.commutator_mono le_rfl hTC).trans
          (Subgroup.commutator_le_right Q C)).trans inf_le_left
    have hQLtwo : IsPGroup 2 (Q ⊓ L : Subgroup G) :=
      (pCore_isPGroup (p := 2) (G := G)).to_inf_left
    have hQLsubNormal : ((Q ⊓ L).subgroupOf L).Normal :=
      (show (Q ⊓ L).Normal from inferInstance).subgroupOf L
    exact hQTleQL.trans
      (normal_pSubgroup_le_core_ambient (Q ⊓ L) L inf_le_right
        hQLtwo hQLsubNormal)
  have hdouble : ⁅⁅Q, T₀⁆, T₀⁆ ≤ V :=
    (Subgroup.commutator_mono hQTleO le_rfl).trans hOT
  have hTcard : Nat.card T₀ = Nat.card T := by
    simpa [T₀] using
      (Subgroup.card_map_of_injective (K := T) C.subtype_injective)
  have hcopQT : Nat.Coprime (Nat.card T₀) (Nat.card Q) := by
    refine Nat.coprime_of_dvd ?_
    intro p hpprime hpT hpQ
    have hpT' : p ∣ Nat.card T := by simpa [hTcard] using hpT
    have hp_not_pi : (⟨p, hpprime⟩ : Nat.Primes) ∉ pi :=
      hTHall.p_in_pi_of_p_dvd_card ⟨p, hpprime⟩ hpT'
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    have hp2 : p = 2 := Nat.prime_eq_prime_of_dvd_pow hpprime Nat.prime_two
      (by simpa [Q, hn] using hpQ)
    exact hp_not_pi hp2
  have hdoubleEq : ⁅⁅Q, T₀⁆, T₀⁆ = ⁅Q, T₀⁆ :=
    Stellmacher.SectionOne.commutator_double_eq_self_of_coprime
      T₀ Q Subgroup.le_normalizer_of_normal hcopQT
  have hQT : ⁅Q, T₀⁆ ≤ V := by
    rw [← hdoubleEq]
    exact hdouble
  exact residual_transfer_of_sup_sylow S V T₀ hgenT hQT

end Stellmacher.SectionTwo
