module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupFusion
public import CFSG.Quasithin.Chapter6.Section02.NaturalBorelGeometry
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# G.2 geometry in the odd-exponent parity argument

The marked Sylow fixed line has Borel stabilizer in L. A Sylow subgroup
supplements its two-residual, so the original local actor contains the
whole Borel and acts irreducibly above the line. The original Cartan and
H normalize the point; its nontrivial normal two-subgroup and condition
(E) give characteristic two in every intermediate Sylow overgroup.
This verifies every clause of G.2.1 on HA and on the full point normalizer.

Residual maximality puts this normalizer inside N_G(O²(H)). G.2.2 supplies
the core, Frattini and commutator bounds on its actual conjugate span.
Global TI, abelianness of that span, the F.8 quotient kernel and the source
5.1.16(2) solvability argument remain with qt-d-1222-linear-field-parity.
No conclusion from those later steps is assumed here.

Source: Aschbacher–Smith, 5.1.17, printed p.640, using G.2.1–2,
printed p.332 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}

/-- The point stabilizer inside L is the original Borel N_L(T∩L). -/
theorem fundamental_point_normalizer
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    L ⊓ (setup T L D.moduleSubgroup H A).G₁ = localBorel T L := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hSm : (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    rw [hS,subgroupOf_map_subtype]
  change L ⊓ normalizer
    ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup : Subgroup G) : Set G) = _
  rw [fundamental_point_eq_sylow_fixed D hTL hpsl hodd]
  simpa only [hSm, localBorel, coe_inf, Set.inf_eq_inter] using hnat.sylow_fixed_normalizer S

/-- The source local residual together with T contains the entire original Borel. -/
theorem fundamental_borel_le_residual_sylow
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    localBorel T L ≤ (setup T L D.moduleSubgroup H A).L₁ ⊔ (T : Subgroup G) := by
  obtain ⟨S,hS⟩ := exists_sylow_localBorel T L hTL
  have he := congrArg (fun X : Subgroup (localBorel T L) => X.map (localBorel T L).subtype)
    (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup,hS,← MonoidHom.range_eq_map,range_subtype] at he
  have hpoint := fundamental_point_normalizer (H := H) (A := A) D hTL hpsl hodd hnat
  have hres : (setup T L D.moduleSubgroup H A).L₁ = residual (localBorel T L) := by
    change residual (L ⊓ (setup T L D.moduleSubgroup H A).G₁) = _
    rw [hpoint]
  rw [hres]
  exact he.ge.trans (sup_le_sup le_rfl inf_le_left)

/-- G.2.1 holds for every overgroup of AT in the full point normalizer. -/
theorem fundamental_g2_at
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : 1 < n)
    (hodd : Odd n) (hnat : IsNaturalModule L D.moduleSubgroup n)
    (c : CartanPair T L H A B)
    (hTJ : (T : Subgroup G) ≤ J) (hAJ : A ≤ J)
    (hJN : J ≤ (setup T L D.moduleSubgroup H A).G₁) :
    (ChapterG.Section02.Setup.mk D.moduleSubgroup
      (setup T L D.moduleSubgroup H A).V₁ L T J).Hypothesis := by
  let Z := (setup T L D.moduleSubgroup H A).V₁
  have hz : Z ≠ ⊥ := by
    intro he
    have hc := fundamental_point_card D hTL hpsl hodd hnat
    change Nat.card Z = 2 ^ n at hc
    rw [he,card_bot] at hc
    have hp : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hZT : Z ≤ (T : Subgroup G) := inf_le_right.trans D.module_le_sylow
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := hTJ.trans hJN
  have hZJ : Z ≤ J := hZT.trans hTJ
  have hcore : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hc : Z ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le hZT) hZJ hJN
    exact hz (bot_unique (hc.trans_eq he))
  have hchar : generalizedFitting J = pCore 2 J :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
        (D.simpleQTKE.evenCharacteristic T) ⟨hcore,hTJ⟩))
  have hpoint := fundamental_point_normalizer (H := H) (A := A) D hTL hpsl hodd hnat
  have hloc : (setup T L D.moduleSubgroup H A).L₁ ≤ localBorel T L :=
    (map_subtype_le _).trans hpoint.le
  have hBJ : localBorel T L ≤ J := by
    rw [← c.left_sup_intersection hTL]
    exact sup_le (inf_le_left.trans hTJ) hAJ
  have hLV : L ≤ normalizer (D.moduleSubgroup : Set G) := by
    obtain ⟨F,_,_,_,_,hm⟩ := hnat
    exact hm.normalizes
  refine {
    elementary := D.module_elementary
    point_ne_bot := hz
    point_le := inf_le_right
    residual := (pResidual_eq_top_iff 2 L).mpr D.faithful.1.2.1
    V_le_T := D.module_le_sylow
    T_normalizes_point := hTZ
    T_normalizes_V := D.sylow_normalizes_module
    T_normalizes_L := hTL
    sylow_LT := ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    H_le := hJN
    local_le := sup_le (hloc.trans hBJ) hTJ
    sylow_H := ⟨T.subtype hTJ,map_subgroupOf_eq_of_le hTJ⟩
    characteristic_two := hchar
    local_normalizes_V := sup_le ((hloc.trans inf_le_left).trans hLV) D.sylow_normalizes_module
    quotient_nonzero := ?_
    irreducible := ?_ }
  · intro he
    have hcard := fundamental_point_card D hTL hpsl hodd hnat
    change Nat.card Z = 2 ^ n at hcard
    change Z = D.moduleSubgroup at he
    rw [he,hnat.card] at hcard
    have hp : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
    rw [pow_mul] at hcard
    nlinarith
  · intro X hZX hXV hNX
    obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
    have hSm : (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
      rw [hS,subgroupOf_map_subtype]
    have he : Z = D.moduleSubgroup ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
      rw [hSm]
      exact fundamental_point_eq_sylow_fixed D hTL hpsl hodd
    have hb := fundamental_borel_le_residual_sylow (H := H) (A := A) D hTL hpsl hodd hnat
    change X = Z ∨ X = D.moduleSubgroup
    rw [he]
    apply hnat.sylow_fixed_invariant_interval S X (he ▸ hZX) hXV
    rw [hSm]
    exact hb.trans hNX

/-- In odd degree the actual H and left Cartan both normalize the chosen point. -/
theorem fundamental_join_le_point_normalizer
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    H ⊔ A ≤ (setup T L D.moduleSubgroup H A).G₁ := by
  have hHC : H ≤ omegaCentralizer T :=
    (residual_le_omegaCentralizer_iff hH.1.1.2).mp
      (residual_centralizes_omega_of_nonfaithful h.qtke hH.1.1 hK.1 hnf)
  have hpoint := fundamental_point_normalizer (H := H) (A := A) D
    h.sylow_normalizes h.linear hodd hnat
  apply sup_le
  · exact (hHC.trans (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  · exact (c.left_le.trans hpoint.ge).trans inf_le_right

/-- The literal HA setup satisfies G.2.1 with no remaining module or local-action premise. -/
theorem fundamental_g2
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    ChapterG.Section02.Setup.Hypothesis (setup T L D.moduleSubgroup H A) :=
  fundamental_g2_at D h.sylow_normalizes h.linear h.exponent hodd hnat c
    ((show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_left) le_sup_right
    (fundamental_join_le_point_normalizer h hH c hodd hK hnf D hnat)

/-- The same construction applies to the full point normalizer, as required by 5.1.17. -/
theorem fundamental_g2_normalizer
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    (ChapterG.Section02.Setup.mk D.moduleSubgroup
      (setup T L D.moduleSubgroup H A).V₁ L T
      (setup T L D.moduleSubgroup H A).G₁).Hypothesis := by
  have hj := fundamental_join_le_point_normalizer h hH c hodd hK hnf D hnat
  exact fundamental_g2_at D h.sylow_normalizes h.linear h.exponent hodd hnat c
    ((show (T : Subgroup G) ≤ H from hH.1.1.2).trans (le_sup_left.trans hj)) (le_sup_right.trans hj) le_rfl

/-- The full point normalizer lies in the original residual normalizer. -/
theorem fundamental_point_normalizer_le_residual_normalizer
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    (setup T L D.moduleSubgroup H A).G₁ ≤ normalizer (residual H : Set G) := by
  let E := setup T L D.moduleSubgroup H A
  have hg := fundamental_g2_normalizer h hH c hodd hK hnf D hnat
  have hz : IsPGroup 2 E.V₁ := T.isPGroup'.to_le
    (hg.point_le.trans D.module_le_sylow)
  have hcore : pCore 2 E.G₁ ≠ ⊥ := by
    intro he
    have hc := le_pCoreIn_of_normalizes hz
      (show E.V₁ ≤ E.G₁ from E.V₁.le_normalizer) (show E.G₁ ≤ normalizer (E.V₁ : Set G) from le_rfl)
    rw [Subgroup.pCoreIn,he,Subgroup.map_bot] at hc
    exact hg.point_ne_bot (bot_unique hc)
  obtain ⟨M,hM,hEM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot E.G₁ hcore
  have hHE := le_sup_left.trans (fundamental_join_le_point_normalizer h hH c hodd hK hnf D hnat)
  have he := residual_unique_of_maximal h.qtke hH.1.1.2 hK M hM (hHE.trans hEM)
  exact he ▸ hEM

/-- G.2.2 gives the source core and almost-special bounds for the full normalizer span. -/
theorem fundamental_normalizer_span_reductions
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    let E := setup T L D.moduleSubgroup H A
    let U := conjugateSpanBy D.moduleSubgroup E.G₁
    U ≤ E.G₁.pCoreIn 2 ∧ U ≤ (T : Subgroup G) ∧
      (frattini U).map U.subtype ≤ E.V₁ ∧ ⁅U,E.G₁.pCoreIn 2⁆ ≤ E.V₁ := by
  have hg := fundamental_g2_normalizer h hH c hodd hK hnf D hnat
  exact ⟨hg.U_le_core,hg.U_normal_in_T.1,hg.frattini_U_le_point,hg.commutator_U_core_le_point⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
