module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCriticalNoncentral
public import Theory.GroupTheory.PGroup.CenterFreeGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NormalCoreProduct
import all CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSNaturalCenter
import all CFSG.Quasithin.Chapter14.Section06.SourceQuinticHyperplanes

/-!
# The original small-quintic middle-core product

The actual quotient of order ten or twenty bounds the image of the whole
middle core.  Its full kernel and the escaping elementary subgroup give a
two-case image calculation.  The proper case contradicts the already proved
noncentrality, using three-core generation and the original marked plane.

The internal imports deliberately reuse the source family's generic plane
minimality, elementary-image bound, and mutual-normalization calculation.
No positive Suzuki parameter or new core-product premise is introduced.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open ChapterF.Source ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]

private theorem small_two_subgroup_card
    {A : Type*} [Group A] [Finite A] (R : Subgroup A)
    (hp : IsPGroup 2 R) (hc : Nat.card A ∣ 20) : Nat.card R ∣ 4 := by
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hcop : (Nat.card R).Coprime 5 := by
    rw [hn]
    exact (by decide : Nat.Coprime 2 5).pow_left n
  exact hcop.dvd_of_dvd_mul_right (R.card_subgroup_dvd_card.trans hc)

private theorem small_quotient_image_dichotomy
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hp : IsPGroup 2 A) (hc : Nat.card B ∣ 20)
    (N D : Subgroup A) (hDN : D ≤ N) (hker : f.ker ≤ N)
    (hD : Nat.card (D.map f) = 2) : N = ⊤ ∨ N = D ⊔ f.ker := by
  have hN : Nat.card (N.map f) ∣ 2^2 :=
    small_two_subgroup_card _ ((hp.to_subgroup N).map f) hc
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hN
  have hlo : 2 ≤ Nat.card (N.map f) := hD ▸ card_le_of_le (map_mono hDN)
  interval_cases k
  · have he0 : Nat.card (N.map f) = 1 := he
    omega
  · right
    have hm : N.map f = D.map f :=
      (eq_of_le_of_card_ge (map_mono hDN) (by rw [hD,he]; decide)).symm
    exact le_antisymm (map_le_map_iff.mp hm.le) (sup_le hDN hker)
  · left
    have hr : Nat.card f.range ≤ 4 := Nat.le_of_dvd (by decide)
      (small_two_subgroup_card _ (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective) hc)
    have hm : N.map f = (⊤ : Subgroup A).map f :=
      eq_of_le_of_card_ge (map_mono le_top) (by
        rw [←MonoidHom.range_eq_map,he]
        exact hr)
    apply top_unique
    have hh := map_le_map_iff.mp hm.ge
    simpa only [sup_of_le_left hker] using hh

private theorem ambient_plane_minimal
    (A V D : Subgroup G) (hVA : V ≤ A) (hc : Nat.card V = 4)
    (hz : center A = ⊥) (hn : A ≤ normalizer (D : Set G)) (hDV : D ≤ V) :
    D = ⊥ ∨ D = V := by
  let : (D.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hn
  have hcard : Nat.card (V.subgroupOf A) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVA).toEquiv).trans hc
  rcases normal_four_minimal_of_centerless (V.subgroupOf A) hcard hz
    (D.subgroupOf A) (subgroupOf_mono A hDV) with he | he
  · left
    have hm := congrArg (Subgroup.map A.subtype) he
    simpa only [map_subgroupOf_eq_of_le (hDV.trans hVA),Subgroup.map_bot] using hm
  · right
    have hm := congrArg (Subgroup.map A.subtype) he
    simpa only [map_subgroupOf_eq_of_le (hDV.trans hVA),map_subgroupOf_eq_of_le hVA] using hm

omit [Finite G] in
private theorem normalizes_commutator_of_normalizes
    (A B C : Subgroup G) (hB : A ≤ normalizer (B : Set G))
    (hC : A ≤ normalizer (C : Set G)) : A ≤ normalizer ((⁅B,C⁆ : Subgroup G) : Set G) := by
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hB ha),
    mem_normalizer_iff_map_conj_eq.mp (hC ha)]

set_option maxHeartbeats 800000 in
/-- The same original critical conjugator gives the full middle-core product,
the exact intersection commutator, and generation of the whole quintic span. -/
theorem source_quintic_middle_core_product
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let UH := conjugateSpanBy (localModule T M) H
    ∃ g ∈ X,
      let Ustar := UH.map (MulAut.conj g).toMonoidHom
      let I := UH ⊓ Ustar
      Ustar ≤ X.pCoreIn 2 ∧ ¬ Ustar ≤ H.pCoreIn 2 ∧
        localModule T M ≤ I ∧ (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        (H.pCoreIn 2 ⊓ X.pCoreIn 2) ⊔
          ((H.pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓ X.pCoreIn 2) = X.pCoreIn 2 ∧
        ⁅I,X.pCoreIn 2⁆ = localModule T M ∧ UH = ⁅UH,H⁆ := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let V := localModule T M
  let Z := centralInvolutions T
  let U := conjugateSpanBy V H
  let Q := X.pCoreIn 2
  let QH := H.pCoreIn 2
  obtain ⟨g,hg,hDQ,hDne,hVI,hTI,hnot⟩ :=
    source_quintic_critical_intersection_noncentral hG T hempty hM hu hmany hcard e H hH hi
  let c := (MulAut.conj g).toMonoidHom
  let D := U.map c
  let Y := QH.map c
  let I := U ⊓ D
  let N := (QH ⊓ Q) ⊔ (Y ⊓ Q)
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow X (T.subtype hTX)).trans_eq (map_subgroupOf_eq_of_le hTX)
  have hQHT : QH ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hTH)).trans_eq (map_subgroupOf_eq_of_le hTH)
  have hQH : Q ≤ H := hQT.trans hTH
  have hQX : Q ≤ X := hQT.trans hTX
  have hQN : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hQHN : H ≤ normalizer (QH : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hmapQ : Q.map c = Q := mem_normalizer_iff_map_conj_eq.mp (hQN hg)
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hUQH : U ≤ QH := by
    obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
      hG T hempty hM hu hmany hcard e
    let := he
    obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
    have hh := hl.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [Section02.rankTwoSeed_eq_localModule] using hh
  have hUQ : U ≤ Q := by
    intro u hu'
    exact (mem_normalizer_iff.mp (hQN hg) u).mpr (hDQ (mem_map_of_mem c hu'))
  have hVQ : V ≤ Q := (le_conjugateSpanBy _ _).trans hUQ
  have hVX : V ≤ X := hVQ.trans hQX
  have hZV : Z ≤ V := le_conjugateSpanBy _ _
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hQcV : Q ≤ centralizer (V : Set G) := by
    have hh := (Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e).1
    exact hh.le.trans inf_le_right
  have hXV : X ≤ normalizer (V : Set G) := by
    rw [←InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
    exact sup_le (sourceResidual_le M Mc) hM.1.2
  have hmapV : V.map c = V := mem_normalizer_iff_map_conj_eq.mp (hXV hg)
  have hZgV : Z.map c ≤ V := (map_mono hZV).trans hmapV.le
  have hcomm : ⁅U,QH⁆ = Z :=
    (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
  have hcommg : ⁅D,Y⁆ = Z.map c := by rw [←map_commutator,hcomm]
  have hZX : center X = ⊥ :=
    (source_quintic_cubic_natural_center hG T hempty hM hu hmany hcard e H hH hi).1
  have hgen : X = (QH ⊔ Y) ⊔ Q := by
    have hT : QH ⊔ Q = (T : Subgroup G) :=
      (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).1
    have hgT : g ∉ (T : Subgroup G) := by
      intro ht
      have hm : U.map c = U := mem_normalizer_iff_map_conj_eq.mp (hHU (hTH ht))
      exact hDne (hm.le.trans hUQH)
    obtain ⟨hF,_,_,hNX,_⟩ := Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
      hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2 (Or.inr hi)
    let S := T.subtype hTX
    let gx : X := ⟨g,hg⟩
    have hS : (S : Subgroup X).map X.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le hTX
    have hR : ((gx • S : Sylow 2 X) : Subgroup X).map X.subtype =
        (T : Subgroup G).map c := by
      change ((S : Subgroup X).map (MulAut.conj gx).toMonoidHom).map X.subtype = _
      rw [←hS,Subgroup.map_map,Subgroup.map_map]
      rfl
    have hne : S ≠ gx • S := by
      intro he
      have hm := congrArg (fun R : Sylow 2 X => (R : Subgroup X).map X.subtype) he
      rw [hS,hR] at hm
      have hn : g ∈ normalizer (T : Set G) := mem_normalizer_iff_map_conj_eq.mpr hm.symm
      exact hgT (hNX ▸ (show g ∈ X ⊓ normalizer (T : Set G) from ⟨hg,hn⟩))
    have hh := CommutingThreeProfile.rankOne_sylow_pair_generates X (hF.quotient 1) S (gx • S) hne
    rw [hS,hR,←hT,Subgroup.map_sup,hmapQ] at hh
    rw [sup_sup_sup_comm,sup_idem] at hh
    exact hh.symm
  have hQHQ : QH ≤ normalizer (Q : Set G) := (hQHT.trans hTX).trans hQN
  have hQQH : Q ≤ normalizer (QH : Set G) := hQH.trans hQHN
  have hYQ : Y ≤ normalizer (Q : Set G) := by
    have hh := (map_mono (f := c) hQHQ).trans (Q.le_normalizer_map c)
    rwa [hmapQ] at hh
  have hQY : Q ≤ normalizer (Y : Set G) := by
    have hh := (map_mono (f := c) hQQH).trans (QH.le_normalizer_map c)
    rwa [hmapQ] at hh
  have hQD : Q ≤ normalizer (D : Set G) := by
    have hh := (map_mono (f := c) (hQH.trans hHU)).trans (U.le_normalizer_map c)
    rwa [hmapQ] at hh
  have hIQ : I ≤ Q := inf_le_left.trans hUQ
  have hIQH : ⁅I,QH⁆ ≤ Z := (commutator_mono inf_le_left le_rfl).trans hcomm.le
  have hIY : ⁅I,Y⁆ ≤ Z.map c := (commutator_mono inf_le_right le_rfl).trans hcommg.le
  have hXI : X ≤ normalizer (I : Set G) := by
    rw [hgen]
    exact sup_le (sup_le
      (le_normalizer_iff_commutator_le_left.mpr (hIQH.trans (hZV.trans hVI)))
      (le_normalizer_iff_commutator_le_left.mpr (hIY.trans (hZgV.trans hVI))))
      ((le_inf (hQH.trans hHU) hQD).trans inf_normalizer_le_normalizer_inf)
  have hXN : X ≤ normalizer (N : Set G) := by
    rw [hgen]
    exact CommutingThreeProfile.sup_normalizes_core_product QH Y Q hQHQ hQQH hYQ hQY
  have hNQ : N ≤ Q := sup_le inf_le_right inf_le_right
  have hDN : D ≤ N := (le_inf (map_mono hUQH) hDQ).trans le_sup_right
  have hcases : N = Q ∨ N = D ⊔ (QH ⊓ Q) := by
    let q := QuotientGroup.mk' (pCore 2 H)
    let f : Q →* (H ⧸ pCore 2 H) := q.comp (inclusion hQH)
    have hker : f.ker = (QH ⊓ Q).subgroupOf Q := by
      ext r
      change q (inclusion hQH r) = 1 ↔ (r : G) ∈ QH ∧ (r : G) ∈ Q
      change (QuotientGroup.mk (inclusion hQH r) : H ⧸ pCore 2 H) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff]
      have hh : inclusion hQH r ∈ pCore 2 H ↔ (r : G) ∈ QH := by
        change inclusion hQH r ∈ pCore 2 H ↔ (r : G) ∈ (pCore 2 H).map H.subtype
        rw [mem_map]; constructor
        · intro hr; exact ⟨inclusion hQH r,hr,rfl⟩
        · rintro ⟨a,ha,he⟩; exact (Subtype.ext he : a = inclusion hQH r) ▸ ha
      rw [hh]
      exact ⟨fun h => ⟨h,r.property⟩,And.left⟩
    let : IsElementaryAbelian 2 U := (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
    let : IsElementaryAbelian 2 D := IsElementaryAbelian.map c
    let : IsElementaryAbelian 2 (D.subgroupOf Q) := IsElementaryAbelian.subgroupOf hDQ
    let : IsElementaryAbelian 2 ((D.subgroupOf Q).map f) := IsElementaryAbelian.map f
    have hm := Section02.SolvableAmalgam.source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi
    have hcardD : Nat.card ((D.subgroupOf Q).map f) = 2 := by
      have hup := quintic_elementary_bound hm ((D.subgroupOf Q).map f)
      have hpos := Nat.card_pos (α := (D.subgroupOf Q).map f)
      have hne : Nat.card ((D.subgroupOf Q).map f) ≠ 1 := by
        intro he
        have hz := card_eq_one.mp he
        apply hDne
        intro d hd
        have hh : f ⟨d,hDQ hd⟩ ∈ (D.subgroupOf Q).map f := mem_map_of_mem f hd
        rw [hz,mem_bot] at hh
        have hh' : (⟨d,hDQ hd⟩ : Q) ∈ f.ker := hh
        rw [hker] at hh'
        exact hh'.1
      omega
    have hc : Nat.card (H ⧸ pCore 2 H) ∣ 20 := by
      rcases hm with hd | hs
      · rw [(Nat.card_congr hd.some.toEquiv).trans DihedralGroup.nat_card]; decide
      · rw [(Nat.card_congr hs.some.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card]
    have hh := small_quotient_image_dichotomy f (pCore_isPGroup.map X.subtype) hc
      (N.subgroupOf Q) (D.subgroupOf Q) (subgroupOf_mono Q hDN)
      (by rw [hker]; exact subgroupOf_mono Q le_sup_left) hcardD
    rcases hh with he | he
    · left
      have hm := congrArg (Subgroup.map Q.subtype) he
      simpa only [map_subgroupOf_eq_of_le hNQ,←MonoidHom.range_eq_map,range_subtype] using hm
    · right
      rw [hker] at he
      have hm := congrArg (Subgroup.map Q.subtype) he
      simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le hNQ,
        map_subgroupOf_eq_of_le (show D ≤ Q from hDQ),map_subgroupOf_eq_of_le (show QH ⊓ Q ≤ Q from inf_le_right)] using hm
  have hprod : N = Q := by
    rcases hcases with he | he
    · exact he
    exfalso
    have hQZ : Q ≤ normalizer (Z : Set G) :=
      (hQcV.trans (centralizer_le hZV)).trans (Subgroup.centralizer_le_normalizer _)
    have hINZ : ⁅I,N⁆ ≤ Z := by
      rw [commutator_comm,he]
      apply commutator_sup_le_of_relative_normal Q D (QH ⊓ Q) I Z hQZ hDQ inf_le_right
      · let : IsElementaryAbelian 2 U := (Section02.SolvableAmalgam.source_index_five_closure_structure
          hG T hempty hM hu hmany hcard e H hH.1 hi).1
        let : IsElementaryAbelian 2 D := IsElementaryAbelian.map c
        have hz : ⁅D,I⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
          ((le_centralizer (H := D)).trans (centralizer_le inf_le_right))
        exact hz.le.trans bot_le
      · rw [commutator_comm]
        exact (commutator_mono le_rfl inf_le_left).trans hIQH
    have hIN : ⁅I,N⁆ = ⊥ := by
      rcases ambient_plane_minimal X V ⁅I,N⁆ hVX hcard hZX
        (normalizes_commutator_of_normalizes X I N hXI hXN) (hINZ.trans hZV) with hh | hh
      · exact hh
      · have hc := card_le_of_le (hh.ge.trans hINZ)
        rw [hcard,hZcard] at hc
        omega
    exact hnot (centralizes_core_of_centralizing_defect X Q I N QH Y V
      (pCore_isPGroup.map X.subtype) hIQ hQX hgen hZX (le_centralizer_iff.mp hQcV)
      (hIQH.trans hZV) (hIY.trans hZgV)
      ((le_inf (le_normalizer_iff_commutator_le_right.mp hQQH)
        (le_normalizer_iff_commutator_le_left.mp hQHQ)).trans le_sup_left)
      ((le_inf (le_normalizer_iff_commutator_le_right.mp hQY)
        (le_normalizer_iff_commutator_le_left.mp hYQ)).trans le_sup_right) hIN)
  have hIQV : ⁅I,Q⁆ ≤ V := by
    rw [←hprod,commutator_comm]
    apply commutator_sup_le_of_relative_normal Q _ _ I V
      (hQcV.trans (Subgroup.centralizer_le_normalizer _)) inf_le_right inf_le_right
    · rw [commutator_comm]
      exact ((commutator_mono le_rfl inf_le_left).trans hIQH).trans hZV
    · rw [commutator_comm]
      exact ((commutator_mono le_rfl inf_le_left).trans hIY).trans hZgV
  have hIQeq : ⁅I,Q⁆ = V := by
    rcases ambient_plane_minimal X V ⁅I,Q⁆ hVX hcard hZX
      (normalizes_commutator_of_normalizes X I Q hXI hQN) hIQV with he | he
    · exact False.elim (hnot (commutator_eq_bot_iff_le_centralizer.mp he))
    · exact he
  have hU : U = ⁅U,H⁆ := by
    apply le_antisymm
    · apply conjugateSpanBy_le
      · exact hIQeq.ge.trans (commutator_mono inf_le_left hQH)
      · exact normalizer_commutator_ge_right U H
    · exact le_normalizer_iff_commutator_le_left.mp hHU
  exact ⟨g,hg,hDQ,hDne,hVI,hTI,hprod,hIQeq,hU⟩

end CFSG.Quasithin.Chapter14.Section06
