module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupNonabelian
public import CFSG.Quasithin.ChapterA.Section01.RankActions.NormalCoprime
public import Theory.GroupTheory.PCoreRestriction

/-!
# Solvable quotient-centralizer bounds in the odd-exponent argument

The original Cartan lies in the literal kernel of the action of N_G(K)
on K/O₂(K). When this kernel is solvable, A.1.26(2) puts every Cartan
commutator from T in O₂(N_G(K)). In particular the entire residual-normalizer
orbit of the natural module lies in that core, and the generated nonabelian
core's Cartan commutator lies in the point-normalizer core.

Independently, the central Cartan image and coprime decomposition show that
C_T(A) cannot be trivial: otherwise H/O₂(H) would have odd order, contrary
to its proved two-rank four. Solvability remains the exact source obligation
5.1.16(2), owned by qt-d-1222-linear-field-parity; it is not asserted here.

Source: Aschbacher–Smith, 5.1.16–17, printed pp.639–641 (refs/quasithin.pdf).
-/

public noncomputable section
open scoped commutatorElement
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

theorem cartan_commutator_le_residual_normalizer_core
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (hRT : R ≤ (T : Subgroup G)) (hAR : A ≤ normalizer (R : Set G)) :
    ⁅R,A⁆ ≤ (normalizer (residual H : Set G)).pCoreIn 2 := by
  let N := normalizer (residual H : Set G)
  let f := normalizerQuotientAction (residual H) (pCore 2 (residual H))
  have hTN : (T : Subgroup G) ≤ N := hH.1.1.2.trans (le_normalizer_residual H)
  have hAN := cartan_normalizes_residual_of_odd h hH c hodd hK hnf
  have hRN : R ≤ N := hRT.trans hTN
  have ha := cartan_residual_action_trivial_of_odd h hH c hodd hK hnf hm
  have hAC : A.subgroupOf N ≤ f.ker := by
    intro a haA
    obtain ⟨b,hb,he⟩ := ha haA
    exact (Subtype.ext he : b = a) ▸ hb
  have hnorm : A.subgroupOf N ≤ normalizer (R.subgroupOf N : Set N) := by
    intro a ha
    exact mem_normalizer_iff.mpr (fun r => mem_normalizer_iff.mp (hAR ha) (r : G))
  have hmax := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_maximal
  have he : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTN)
      (le_componentOrbit _ _)
  rw [he] at hmax
  have hsq : IsStronglyQuasithin N := (h.qtke.twoLocal_sqtk hmax.1).stronglyQuasithin
  let : Group.IsSolvable f.ker := hsolv
  have hb := ChapterA.normal_solvable_coprime_commutator_le_core f.ker
    (A.subgroupOf N) (R.subgroupOf N) (hsq.subgroup f.ker) hAC
    (by
      rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ N from hAN)).toEquiv]
      exact cartan_card_coprime_six_of_odd c h.sylow_normalizes h.linear hodd)
    (T.isPGroup'.to_le hRT).comap_subtype hnorm
  have hc : f.ker.pCoreIn 2 ≤ pCore 2 N := by
    have he : pCore 2 f.ker = (pCore 2 N).comap f.ker.subtype :=
      pCore_eq_comap_of_normal 2 f.ker
    change (pCore 2 f.ker).map f.ker.subtype ≤ _
    rw [he]
    exact map_comap_le _ _
  have hi := map_mono (f := N.subtype) (hb.trans hc)
  rwa [map_commutator,map_subgroupOf_eq_of_le hRN,map_subgroupOf_eq_of_le hAN] at hi

theorem fundamental_orbit_le_residual_normalizer_core
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    conjugateSpanBy D.moduleSubgroup (normalizer (residual H : Set G)) ≤
      (normalizer (residual H : Set G)).pCoreIn 2 := by
  let N := normalizer (residual H : Set G)
  have hAV : A ≤ normalizer (D.moduleSubgroup : Set G) := by
    obtain ⟨F,_,_,_,_,hm⟩ := hnat
    exact (c.left_le.trans inf_le_left).trans hm.normalizes
  have hv := cartan_commutator_le_residual_normalizer_core h hH c hodd hK hnf hm hsolv
    D.module_le_sylow hAV
  rw [← fundamental_cartan_commutator D h.sylow_normalizes h.linear h.exponent c hnat] at hv
  apply conjugateSpanBy_le hv
  change N ≤ normalizer ((pCore 2 N).map N.subtype : Set G)
  simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 N).le_normalizer_map N.subtype

theorem fundamental_nonabelian_cartan_layers_le_core
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L D.moduleSubgroup).U)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L D.moduleSubgroup).G₁) :
    let E := normalizerSetup T L D.moduleSubgroup
    ⁅E.S l,A⁆ ⊔ E.S₂ l ≤ E.QH := by
  let E := normalizerSetup T L D.moduleSubgroup
  have hg := fundamental_g2_normalizer h hH c hodd hK hnf D hnat
  change E.Hypothesis at hg
  obtain ⟨F,_,_,⟨d⟩⟩ := fundamental_nonabelian_marking h hH c hodd hK hnf D hnat hnon hl hlout
  have hut := hg.U_normal_in_T.1
  have hf := hg.frattini_U_le_point
  have hST : E.S l ≤ (T : Subgroup G) := by
    rw [d.S_eq_star_kernel hut hf]
    exact inf_le_right.trans ((pCoreIn_le_sylow E.LT
      (T.subtype (show (T : Subgroup G) ≤ E.LT from le_sup_right))).trans
        (map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ E.LT from le_sup_right)).le)
  have hAS : A ≤ normalizer (E.S l : Set G) :=
    ((c.left_le.trans inf_le_left).trans (d.L_le_I hut hf)).trans
      ChapterG.Section02.RankOneHigherFields.Hypothesis.I_normalizes_core
  have hc := cartan_commutator_le_residual_normalizer_core h hH c hodd hK hnf hm hsolv hST hAS
  have hEN := fundamental_point_normalizer_le_residual_normalizer h hH c hodd hK hnf D hnat
  have hTH : (T : Subgroup G) ≤ E.H := le_sup_right.trans hg.local_le
  have hbound : ⁅E.S l,A⁆ ≤ E.QH :=
    (le_inf ((le_normalizer_iff_commutator_le_left.mp hAS).trans (hST.trans hTH)) hc).trans
      (inf_pCoreIn_le_of_le 2 hEN)
  exact sup_le hbound (inf_le_left.trans hg.U_le_core)

theorem sylow_cartan_centralizer_ne_bot
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    (T : Subgroup G) ⊓ centralizer (A : Set G) ≠ ⊥ := by
  intro hz
  have hAT := cartan_normalizes_sylow_of_odd c h.sylow_normalizes h.linear hodd
  have hcop : Nat.Coprime (Nat.card A) (Nat.card T) := by
    obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
    rw [hk]
    exact ((cartan_card_coprime_six_of_odd c h.sylow_normalizes h.linear hodd).of_dvd_right
      (by decide : 2 ∣ 6)).pow_right k
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hmove := eq_commutator_sup_centralizer_of_solvable_coprime
    (T : Subgroup G) A hAT inferInstance hcop
  rw [hz,sup_bot_eq] at hmove
  let J := H ⊔ A
  let q := QuotientGroup.mk' (pCore 2 J)
  have hTJ : (T : Subgroup G) ≤ J :=
    (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_left
  have hc := cartan_image_central_of_odd h hH c hodd hK hnf hm
  have hcomm : ⁅(T : Subgroup G),A⁆ ≤ J.pCoreIn 2 := by
    apply commutator_le.mpr
    intro t ht a ha
    let tj : J := ⟨t,hTJ ht⟩
    let aj : J := ⟨a,mem_sup_right ha⟩
    have hcom : Commute (q tj) (q aj) := mem_center_iff.mp
      (hc (mem_map_of_mem q (show aj ∈ A.subgroupOf J from ha))) (q tj)
    have hk : ⁅tj,aj⁆ ∈ pCore 2 J := (QuotientGroup.eq_one_iff _).mp
      (by change q ⁅tj,aj⁆ = 1; rw [map_commutatorElement]; exact hcom.commutator_eq)
    exact mem_map_of_mem J.subtype hk
  have hTcore : (T : Subgroup G) ≤ H.pCoreIn 2 := by
    rw [hmove]
    rw [pCoreIn_sup_eq_of_sylow_le hH.1.1.2
      (cartan_normalizes_outside_of_odd h hH c hodd hK hnf)] at hcomm
    exact hcomm
  let qH := QuotientGroup.mk' (pCore 2 H)
  let P := (T.subtype hH.1.1.2).mapSurjective (f := qH) (QuotientGroup.mk'_surjective _)
  have hp : (P : Subgroup (H ⧸ pCore 2 H)) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro t ht
    have hh := hTcore ht
    change qH t = 1
    apply (QuotientGroup.eq_one_iff t).mpr
    exact (mem_map_iff_mem H.subtype_injective).mp hh
  have hn2 : ¬ 2 ∣ Nat.card (H ⧸ pCore 2 H) := by
    have hh := P.not_dvd_index
    rw [hp,index_bot] at hh
    exact hh
  have hzero := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn2
  rw [residual_sylow_extension_two_rank hH.1.1.2 hm] at hzero
  omega
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
