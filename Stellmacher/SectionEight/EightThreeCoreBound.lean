module
public import Stellmacher.SectionEight.EightThreeLocalFamily
public import Stellmacher.SectionEight.EightThreeCharacteristicObstruction
public import Stellmacher.SectionTwo.NormalSupplementPrescribedCore
public import Stellmacher.SectionFiveToSeven.VertexLocalModule
public import Stellmacher.SectionFiveToSeven.PFamilyInjective
public import Stellmacher.UniqueMaximalContainingTransport
/-!
# The original center-module core bound in Stellmacher (8.3)

Assume the initial residual core lies in the next vertex core, with the
actual local Section Eight context and critical path. Then [Qa,Ea] lies in Za,
and Za lies in the next vertex core. The neighboring centrality assumption
is not needed here; the subsequent center-free collapse uses it. The legacy
context theorem is retained as an exact wrapper through `toLocalContext`.

Transport the normal supplement Ea Qfirst into the native group Ga with
its exact Sylow image Qfirst. The graph vertex-module theorem identifies
the original Section Two module with Za. The critical-edge centralizer
equality gives O2(Ga)=C_S(Za), and the Sylow-center join puts Omega1(Z(S))
inside Qfirst. The normal-supplement Baumann theorem therefore puts Za in
the Baumann subgroup B of Qfirst and makes B Sylow in its Ga-normal closure.

If B lay in Qa, that normal closure would be a two-group, forcing B to be
normal in Ga. The next stabilizer also normalizes B, so the actual generating
edge pair would make B a normal ambient two-subgroup. The two-group property
uses the actual edge Sylow inside Ga and its ambient image S, with no assumption
that S lies in a specified ambient Sylow. Its triviality would
contradict Za's nonzero commutator with the opposite critical center. Thus
B is outside Qa. The injection-based characteristic obstruction applies to
every required native factor. Prescribed-module pushing-up then gives
[Qa,Ea] inside the unchanged Za, with the residual transported by its actual
subtype map. This implies the source's residual-core bound and permits the
two center-free collapses to be combined by the following module.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.3), p38,
refs/latex/stellmacher-n-group.tex. The proof expands the normal-supplement
use of (2.3),(2.4), retaining the prescribed module rather than identifying
different Sylow-center normal closures.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The prescribed-module bound and containment for Stellmacher (8.3). -/
public theorem eight_three_core_bound_data_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcontained : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.firstStep) :
    (⁅QAt ctx.Γ ctx.criticalPath.a, EAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a) ∧
      ZAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  classical
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Pb := stabilizer Γ cp.firstStep
  let T := q Γ cp.firstStep
  let EA := e Γ cp.a
  let LA := EA ⊔ T
  let N := LA.subgroupOf P
  have hloc := (SevenSix.edge_local_data h Γ cp).1
  have hPset := (pFamily_iff_pSet _ _ _).mp hloc.1
  obtain ⟨hSP,U,hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  have hUne : (U : Subgroup P) ≠ ⊥ := by
    intro hb
    apply h.S_nontrivial
    rw [← hU,hb,Subgroup.map_bot]
  have heven : Even (Nat.card P) := by
    have hd : 2 ∣ Nat.card U := U.isPGroup'.card_eq_or_dvd.resolve_left
      (fun hc => hUne (Subgroup.card_eq_one.mp hc))
    exact even_iff_two_dvd.mpr (hd.trans (Subgroup.card_subgroup_dvd_card (U : Subgroup P)))
  have hsec : SectionTwo.Hypotheses P :=
    ⟨hloc.2,heven,(SevenSix.edge_characteristic_data h Γ cp).1⟩
  have h3 : SectionThree.Hypotheses P (U : Subgroup P) := ⟨heven,hUne,U.isPGroup'⟩
  have hcoreNe : pCore 2 P ≠ ⊥ := by
    intro hb
    apply hPset.1.2.2.1
    change (pCore 2 P).map P.subtype = ⊥
    rw [hb,Subgroup.map_bot]
  have hUneCore : (U : Subgroup P) ≠ pCore 2 P := by
    intro he
    apply hPset.1.2.2.2
    exact hU.symm.trans (congrArg (fun A : Subgroup P => A.map P.subtype) he)
  have huniq : IsUniqueMaximalContaining (U : Subgroup P) (⊤ : Subgroup P) :=
    native_uniqueMaximalContaining P (U : Subgroup P) (by rw [hU]; exact hPset.2)
  have hnative : (⊤ : Subgroup P) ∈ SectionThree.PSet ⊤ (U : Subgroup P) := by
    have hh := pFamily_range_of_injective (MonoidHom.id P) Function.injective_id U
      (U : Subgroup P) (Subgroup.map_id _) hcoreNe hUneCore huniq
    rw [(MonoidHom.id P).range_eq_top_of_surjective Function.surjective_id,pFamily_iff_pSet] at hh
    exact hh
  obtain ⟨hLset,hLN,hLAgen,hTnot⟩ := eight_three_normal_supplement_local ctx hcontained
  change LA ∈ SectionThree.LSet ⊤ T at hLset
  change NormalIn LA P at hLN
  have hLAP := hLN.1
  let _ : N.Normal := hLN.2
  have hTS : T ≤ S := (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hTP : T ≤ P := hTS.trans hSP
  obtain ⟨QL,hQL⟩ := hLset.2.1
  let eN : N ≃* LA := Subgroup.subgroupOfEquivOfLe hLAP
  let Q : Sylow 2 N := QL.mapSurjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  have hQmap : ((Q : Subgroup N).map N.subtype).map P.subtype = T := by
    change (((QL : Subgroup LA).map eN.symm.toMonoidHom).map N.subtype).map P.subtype = T
    rw [Subgroup.map_map,Subgroup.map_map]
    exact hQL
  let TN := (Q : Subgroup N).map N.subtype
  have hTN : TN = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTP]
    exact hQmap
  have hQS : TN ≤ (U : Subgroup P) := by
    rw [hTN,hUS]
    exact Subgroup.subgroupOf_mono P hTS
  have hNgen : N ⊔ (U : Subgroup P) = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup,hU,Subgroup.map_subgroupOf_eq_of_le hLAP,
      ← MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact hLAgen
  have hPbT : Pb ≤ Subgroup.normalizer (T : Set H) := SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep
  have hSPb : S ≤ Pb := (SevenSix.edge_sylow_data h Γ cp).2.1
  have hST : S ≤ Subgroup.normalizer (T : Set H) := hSPb.trans hPbT
  have hSN : (U : Subgroup P) ≤ Subgroup.normalizer (TN : Set P) := by
    rw [hTN,hUS]
    exact (Subgroup.le_normalizer_comap P.subtype).trans' (Subgroup.comap_mono hST)
  have hQne : (Q : Subgroup N) ≠ ⊥ := by
    intro hb
    change ¬ T ≤ _ at hTnot
    apply hTnot
    have hTb : T = ⊥ := by rw [← hQmap,hb,Subgroup.map_bot,Subgroup.map_bot]
    rw [hTb]
    exact bot_le
  let V := SectionTwo.vSubgroup U
  have hVmap : V.map P.subtype = z Γ cp.a := vertexZ_eq_local_vSubgroup Γ cp.a U
  have hZQ : SectionTwo.zSubgroup U ≤ TN := by
    have hOm : omegaOneCenter S ≤ z Γ cp.firstStep := by
      obtain ⟨_,Ub,hUb⟩ := (SevenSix.edge_sylow_data h Γ cp).2
      rw [z,Γ.zAt_def]
      apply le_sSup
      exact ⟨Ub,congrArg omegaOneCenter hUb.symm⟩
    have hfirst : cp.a ∈ neighborhood Γ cp.firstStep :=
      (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
    have hzT : z Γ cp.firstStep ≤ T :=
      ((lemma_seven_three h Γ).center_core cp.firstStep cp.a hfirst).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [hQmap]
    change (omegaOneCenterAmbient (U : Subgroup P)).map P.subtype ≤ _
    rw [← omegaOneCenterAmbient_map_injective P.subtype P.subtype_injective,hU]
    exact hOm.trans hzT
  have hcore : pCore 2 P = (U : Subgroup P) ⊓ Subgroup.centralizer (V : Set P) := by
    have hedge := (lemma_seven_four h Γ cp).edge_centralizer
    ext x
    have hxQ : x ∈ pCore 2 P ↔ (x : H) ∈ q Γ cp.a := by
      rw [q,Γ.twoCoreAt_def]
      exact (Subgroup.mem_map_iff_mem (f := P.subtype) P.subtype_injective).symm
    rw [hxQ,← hedge]
    change ((x : H) ∈ S ∧ (x : H) ∈ Subgroup.centralizer (z Γ cp.a : Set H)) ↔
      x ∈ (U : Subgroup P) ∧ x ∈ Subgroup.centralizer (V : Set P)
    rw [hUS]
    apply and_congr Iff.rfl
    rw [← hVmap,Subgroup.mem_centralizer_iff,Subgroup.mem_centralizer_iff]
    constructor
    · intro hx v hv
      exact Subtype.ext (hx v (Subgroup.mem_map_of_mem P.subtype hv))
    · intro hx v hv
      obtain ⟨w,hw,rfl⟩ := hv
      exact congrArg Subtype.val (hx w hw)
  let B := TN ⊓ Subgroup.centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ TN) : Set P)
  let BA := baumannIn T
  have hBmap : B.map P.subtype = BA := by
    rw [show B = TN ⊓ Subgroup.centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ TN) : Set P) from rfl,
      baumann_map_injective P.subtype P.subtype_injective,hQmap]
    rfl
  have hBAS : BA ≤ S := inf_le_left.trans hTS
  have hPbB : Pb ≤ Subgroup.normalizer (BA : Set H) :=
    hPbT.trans (normalizer_le_normalizer_baumann T)
  have hsetup := SectionTwo.normal_supplement_baumann_setup hsec U N Q hNgen hQS hSN hZQ hQne hcore
  change V ≤ B ∧ IsSylowSubgroupIn B (Subgroup.normalClosure (B : Set P)) at hsetup
  have hZaT : z Γ cp.a ≤ T := by
    rw [← hVmap,← hQmap]
    exact Subgroup.map_mono (hsetup.1.trans inf_le_left)
  refine ⟨?_,hZaT⟩
  have hBnot : ¬ B ≤ pCore 2 P := by
    intro hBcore
    let L := Subgroup.normalClosure (B : Set P)
    have hLcore : L ≤ pCore 2 P := Subgroup.normalClosure_le_normal hBcore
    have hL2 : IsPGroup 2 L := (pCore_isPGroup (p := 2) (G := P)).to_le hLcore
    obtain ⟨PB,hPB⟩ := hsetup.2
    change (PB : Subgroup L).map L.subtype = B at hPB
    have hPBtop : (PB : Subgroup L) = ⊤ :=
      (PB.is_maximal' (hL2.to_subgroup ⊤) le_top).symm
    have hBL : B = L := by
      rw [← hPB,hPBtop,← MonoidHom.range_eq_map,Subgroup.range_subtype]
    let _ : B.Normal := hBL ▸ Subgroup.normalClosure_normal
    have hPBA : P ≤ Subgroup.normalizer (BA : Set H) := by
      rw [← hBmap]
      have hh := Subgroup.le_normalizer_map (H := B) P.subtype
      rwa [Subgroup.normalizer_eq_top,← MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    have hcover : P ⊔ Pb = ⊤ := by
      rcases cp.edge_stabilizers_are_P with he | he
      · rw [show P = P1 from he.1,show Pb = P2 from he.2,ctx.sectionSeven.generated]
      · rw [show P = P2 from he.1,show Pb = P1 from he.2,sup_comm,ctx.sectionSeven.generated]
    have hBAN : BA.Normal := Subgroup.normalizer_eq_top_iff.mp (top_unique (by
      rw [← hcover]
      exact sup_le hPBA hPbB))
    have hS2 : IsPGroup 2 S := by
      rw [← hU]
      exact U.isPGroup'.map P.subtype
    have hBA2 : IsPGroup 2 BA := hS2.to_le hBAS
    have hBAzero : BA = ⊥ := le_bot_iff.mp
      ((show BA ≤ pCore 2 H from le_sSup ⟨hBAN,hBA2⟩).trans_eq h.twoCore_eq_bot)
    have hVzero : z Γ cp.a = ⊥ := by
      apply le_bot_iff.mp
      rw [← hVmap]
      exact (Subgroup.map_mono hsetup.1).trans_eq (hBmap.trans hBAzero)
    apply ctx.commutator_ne
    rw [hVzero,Subgroup.commutator_bot_left]
  have hchar : ∀ (K : Subgroup P) (PK : Sylow 2 K),
      (PK : Subgroup K).map K.subtype = B → K ⊔ (U : Subgroup P) = ⊤ →
      ∀ A : Subgroup PK, A.Characteristic → A ≠ ⊥ →
        ¬ (A.map (PK : Subgroup K).subtype).Normal := by
    intro K PK hPK hKgen
    let f := P.subtype.comp K.subtype
    have hf : Function.Injective f := P.subtype_injective.comp K.subtype_injective
    have hPKA : (PK : Subgroup K).map f = BA := by
      rw [show f = P.subtype.comp K.subtype from rfl,← Subgroup.map_map,hPK,hBmap]
    have hKgenA : f.range ⊔ S = P := by
      rw [show f = P.subtype.comp K.subtype from rfl,MonoidHom.range_comp,Subgroup.range_subtype,
        ← hU,← Subgroup.map_sup,hKgen,← MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact eight_three_normalized_image_obstruction_of_injective_local ctx BA hBAS hPbB f hf PK hPKA hKgenA
  have hc := SectionTwo.normal_supplement_core_residual_le_module hsec U h3 hnative
    N Q hNgen hQS hSN hZQ hQne hcore hBnot hchar
  have hm := Subgroup.map_mono (f := P.subtype) hc
  rw [Subgroup.map_commutator,hVmap] at hm
  change ⁅(pCore 2 P).map P.subtype, (twoResidualAmbient (⊤ : Subgroup P)).map P.subtype⁆ ≤ _ at hm
  have hr := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) P.subtype P
    (by rw [← MonoidHom.range_eq_map,Subgroup.range_subtype])
  rw [hr] at hm
  change ⁅q Γ cp.a,e Γ cp.a⁆ ≤ z Γ cp.a
  rw [q,Γ.twoCoreAt_def,CosetGraphContext.e,Γ.twoResidualAt_def]
  exact hm

/-- The prescribed-module bound and containment for Stellmacher (8.3). -/
public theorem eight_three_core_bound_data
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcontained : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.firstStep) :
    (⁅QAt ctx.Γ ctx.criticalPath.a, EAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a) ∧
      ZAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  exact eight_three_core_bound_data_local ctx.toLocalContext hcontained
end Stellmacher.SectionEight

