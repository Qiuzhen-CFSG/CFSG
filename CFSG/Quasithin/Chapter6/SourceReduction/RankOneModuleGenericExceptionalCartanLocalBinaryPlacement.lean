module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryModule
public import Theory.SpecificGroups.Triality.BinaryCentralOddOrder

/-!
# Point-centralizer placement of the original binary-triality minus torus

The actual minus torus fixes a nonidentity point of the original Sylow
omega-center. Source 1.2.4 embeds the entire original triality component
in a normal C-component of that point centralizer. The original inverter
lies in this component, so inversion modulo the original Sylow puts the
odd torus inside it. Its order survives the full two-core quotient, and
the image of the original component retains its intrinsic two-core quotient.

If the torus lies in the original component, its marked central-parabolic
image has odd order dividing 21. Its order 2^(n/2)+1 then forces n=2.
Consequently the constructed point component either strictly enlarges the
original component or the original left degree is two. The same escaping
cubic, inverter, residual, both Hall conditions and original W are retained.

This is actual component placement, not an exceptional-model classification.
Excluding this remaining binary branch and completing the other containing
rows are still required for LocalCartanSieve and SourceLocalCartanEscape.
Source: Aschbacher--Smith 1.2.4 and 5.1.13, printed pp.505,635--638,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem point_mem_H {z : G} (hz : orderOf z = 2) :
    centralizer ({z} : Set G) ∈ Chapter1.H G := by
  obtain ⟨Q,hQ,hp,he⟩ := isTwoLocal_involution_centralizer hz
  rw [he]
  have hc : Q ≤ (normalizer (Q : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp Q.le_normalizer le_rfl
  exact fun hh => hQ (bot_unique (hc.trans_eq hh))

omit [Finite G] in
private theorem local_of_relative_component
    {T : Sylow 2 G} {X Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (hY : Y ∈ Chapter1.H G)
    (hXY : X ≤ Y) (hX : (X.subgroupOf Y).IsCComponent) :
    X ∈ Chapter1.L G (T : Subgroup G) := by
  refine ⟨hX.subgroupOf_of_le le_sup_left (sup_le hXY hTY),
    ⟨T.subtype le_sup_right,?_⟩,?_⟩
  · simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
  · intro hz
    exact hY (bot_unique
      ((pCoreIn_le_pCoreIn_of_sylow T le_sup_right (sup_le hXY hTY)).trans_eq hz))

/-- Inversion puts an odd actor inside an actual normal containing component
of the specified local overgroup. The selected local component is retained. -/
theorem inverted_odd_point_placement
    {T : Sylow 2 G} {X E : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hX : X ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hXC : X ≤ omegaCentralizer T) (ho : Odd (Nat.card E))
    {z t : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hEz : E ≤ centralizer ({z} : Set G)) (htX : t ∈ X)
    (hi : ∀ x ∈ E, t*x*t⁻¹*x ∈ (T : Subgroup G)) :
    ∃ J : Subgroup G, X ≤ J ∧ J ≤ centralizer ({z} : Set G) ∧
      (J.subgroupOf (centralizer ({z} : Set G))).IsCComponent ∧
      (J.subgroupOf (centralizer ({z} : Set G))).Normal ∧
      J ∈ Chapter1.L G (T : Subgroup G) ∧ E ≤ J := by
  let P := centralizer ({z} : Set G)
  have hCP : omegaCentralizer T ≤ P :=
    centralizer_le (Set.singleton_subset_iff.mpr hz)
  have hXP := hXC.trans hCP
  have hTP := (sylow_le_omegaCentralizer (T := T)).trans hCP
  have hP : P ∈ Chapter1.H G := point_mem_H
    (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1)
  let S := T.subtype hTP
  have hx : X.subgroupOf P ∈ Chapter1.L P (S : Subgroup P) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTP hXP).mp ⟨hXP,hX⟩
  have hnx : (S : Subgroup P) ≤ normalizer (X.subgroupOf P : Set P) := by
    rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hXP]
    exact comap_mono hn
  obtain ⟨C,⟨hC,hXC',hCn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hP) S hx hnx
  let J := C.map P.subtype
  have hJP : J ≤ P := map_subtype_le C
  have hXJ : X ≤ J := by
    simpa only [map_subgroupOf_eq_of_le hXP] using map_mono (f := P.subtype) hXC'
  have hc : (J.subgroupOf P).IsCComponent := by
    change (C.map P.subtype |>.comap P.subtype).IsCComponent
    simpa only [comap_map_eq_self_of_injective P.subtype_injective] using hC
  have hnormal : (J.subgroupOf P).Normal := by
    change (C.map P.subtype |>.comap P.subtype).Normal
    simpa only [comap_map_eq_self_of_injective P.subtype_injective] using hCn
  have hPN : P ≤ normalizer (J : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hJP).mp hnormal
  exact ⟨J,hXJ,hJP,hc,hnormal,local_of_relative_component hTP hP hJP hc,
    Theory.GroupTheory.odd_inverted_mod_two_le ho (hEz.trans hPN) T.isPGroup' (hXJ htX) hi⟩

private theorem odd_core_image_card {E J : Subgroup G}
    (hEJ : E ≤ J) (ho : Odd (Nat.card E)) :
    Nat.card ((E.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = Nat.card E := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let D := E.subgroupOf J
  have hd : Disjoint D q.ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hEJ).toEquiv]
    exact ho.coprime_two_right.pow_right k
  have hqi : Function.Injective (q.subgroupMap D) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨x.property,
      congrArg Subtype.val (show q.subgroupMap D x = 1 from hx)⟩))
  exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap D)
    ⟨hqi,q.subgroupMap_surjective D⟩).toEquiv).symm.trans
    (Nat.card_congr (subgroupOfEquivOfLe hEJ).toEquiv)

private theorem original_core_image_equiv {Y J : Subgroup G} (C : Subgroup Y)
    (hCJ : C.map Y.subtype ≤ J) :
    Nonempty ((C ⧸ pCore 2 C) ≃*
      (((C.map Y.subtype).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ⧸
        pCore 2 (((C.map Y.subtype).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))))) := by
  let e := (C.equivMapOfInjective Y.subtype Y.subtype_injective).trans
    (subgroupOfEquivOfLe hCJ).symm
  let q := QuotientGroup.mk' (pCore 2 J)
  let D := (C.map Y.subtype).subgroupOf J
  have hk : IsPGroup 2 (q.subgroupMap D).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((q.subgroupMap D).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective D) hk)⟩


private theorem torus_degree_two_of_original_placement
    {T : Sylow 2 G} {L W H A B K Y E : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C))
    (hEA : E ≤ A) (hEC : E ≤ C.map Y.subtype)
    (hn : n = 2*(n/2)) (hEc : Nat.card E = 2^(n/2)+1) : n = 2 := by
  obtain ⟨e,_,_,hcases⟩ := LocalSieve.binaryTriality_escape_central_placement
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Cbar := C.map q
  let Ebar := (E.subgroupOf Y).map q
  let J := (A.subgroupOf Y).map q ⊔ ((T : Subgroup G).subgroupOf Y).map q
  have hECY : E.subgroupOf Y ≤ C := by
    change E.comap Y.subtype ≤ C
    have hh := comap_mono (f := Y.subtype) hEC
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hEB : Ebar ≤ Cbar := map_mono hECY
  have hEJ : Ebar ≤ J := (map_mono (comap_mono hEA)).trans le_sup_left
  let F := (Ebar.subgroupOf Cbar).map e.toMonoidHom
  have hF : F ≤ Triality.Standard.Parabolics.parabolic
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .central := by
    have hx := map_mono (f := e.toMonoidHom) (comap_mono (f := Cbar.subtype) hEJ)
    rcases hcases with he | he
    · exact hx.trans (he ▸ Triality.Standard.Parabolics.localFactor_le_parabolic _ .central)
    · exact hx.trans_eq he
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have ho := hoA.of_dvd_nat (card_dvd_of_le hEA)
  have hFc : Nat.card F = Nat.card E := by
    rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv]
    exact odd_core_image_card (hEC.trans (map_subtype_le C)) ho
  have hd := Triality.Standard.BinaryCentralOddOrder.card_dvd_twentyOne F (hFc.symm ▸ ho) hF
  rw [hFc,hEc] at hd
  have hb : 2^(n/2) < 2^5 := by
    have := Nat.le_of_dvd (by decide : 0 < 21) hd
    omega
  have hh : n/2 < 5 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hb
  interval_cases hx : n/2 <;> norm_num at hd
  omega


/-- The original minus torus lies in a normal component of the centralizer
of its nonidentity omega-point. This component contains the entire original
binary-triality component. Either the original degree is two or this is a
strict enlargement. Both original quotient kernels and the torus order survive. -/
theorem original_minus_torus_point_component
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    n % 4 = 2 ∧
      ∃ (D E J : Subgroup G) (t z : G),
        D ≤ A ∧ D ≤ C.map Y.subtype ∧ Nat.card D = 3 ∧
        ¬ D ≤ normalizer (residual H : Set G) ∧
        t ∈ (T : Subgroup G) ⊓ C.map Y.subtype ∧ t ∉ L ∧
        (∀ d ∈ D, t*d*t⁻¹=d⁻¹) ∧
        E ≤ A ∧ D ≤ E ∧ Nat.card E = 2^(n/2)+1 ∧
        (∀ x : G, x ∈ E ↔ x ∈ A ∧ x^(2^(n/2)+1)=1) ∧
        z ∈ omegaOneCenterAmbient (T : Subgroup G) ∧ z ≠ 1 ∧
        E ≤ centralizer ({z} : Set G) ∧
        (∀ x ∈ E, t*x*t⁻¹*x ∈ (T : Subgroup G)) ∧
        C.map Y.subtype ≤ J ∧ residual H ≤ J ∧ J ≤ centralizer ({z} : Set G) ∧
        (J.subgroupOf (centralizer ({z} : Set G))).IsCComponent ∧
        (J.subgroupOf (centralizer ({z} : Set G))).Normal ∧
        J ∈ Chapter1.L G (T : Subgroup G) ∧ E ≤ J ∧
        Nat.card ((E.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 2^(n/2)+1 ∧
        Nonempty ((C ⧸ pCore 2 C) ≃*
          (((C.map Y.subtype).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ⧸
            pCore 2 (((C.map Y.subtype).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))))) ∧
        (n = 2 ∨ C.map Y.subtype < J) ∧
        centralizer ({z} : Set G) ∈ Chapter1.HOver G (H : Set G) ∧
        ¬ A ⊓ centralizer ({z} : Set G) ≤ normalizer (residual H : Set G) := by
  obtain ⟨hn,D,E,t,z,hDA,hDC,hDc,hDn,ht,htL,hi,hEA,hDE,hEc,hroot,hz,hz1,hEz,hinv⟩ :=
    original_inverted_minus_torus h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hc := original_container_centralizes h hH c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hKR,hCn⟩ := LocalSieve.binaryTriality_seed_eq_residual_and_normal h.qtke hKH hH.1.1.2
    hK hKT horbit hY hescape C hC hKC hm
  let X := C.map Y.subtype
  have hXY : X ≤ Y := map_subtype_le C
  have hcomp : (X.subgroupOf Y).IsCComponent := by
    change (C.map Y.subtype |>.comap Y.subtype).IsCComponent
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hC
  have hnormal : (X.subgroupOf Y).Normal := by
    change (C.map Y.subtype |>.comap Y.subtype).Normal
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hCn
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    (hH.1.1.2.trans hY.2).trans ((normal_subgroupOf_iff_le_normalizer hXY).mp hnormal)
  have hX := local_of_relative_component (hH.1.1.2.trans hY.2) hY.1 hXY hcomp
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have ho := hoA.of_dvd_nat (card_dvd_of_le hEA)
  obtain ⟨J,hXJ,hJz,hJc,hJn,hJ,hEJ⟩ :=
    inverted_odd_point_placement h.qtke hX hTX hc ho hz hz1 hEz ht.2 hinv
  refine ⟨hn,D,E,J,t,z,hDA,hDC,hDc,hDn,ht,htL,hi,hEA,hDE,hEc,hroot,hz,hz1,hEz,hinv,
    hXJ,(hKR ▸ hKC).trans hXJ,hJz,hJc,hJn,hJ,hEJ,(odd_core_image_card hEJ ho).trans hEc,
    original_core_image_equiv C hXJ,?_,?_,?_⟩
  · by_cases he : X = J
    · left
      exact torus_degree_two_of_original_placement h hH hgen c hKH hK hKT horbit hY
        hescape C hC hKC hm hEA (hEJ.trans_eq he.symm) (by omega) hEc
    · exact Or.inr (lt_of_le_of_ne hXJ he)
  · refine ⟨point_mem_H (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1),?_⟩
    exact ((residual_le_omegaCentralizer_iff hH.1.1.2).mp ((hKR ▸ hKC).trans hc)).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hz))
  · exact fun hN => hDn ((le_inf hDA (hDE.trans hEz)).trans hN)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
