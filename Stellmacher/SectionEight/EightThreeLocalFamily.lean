module
public import Stellmacher.LaterDefs
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionThree.NormalSupplementFamilySelection
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction
public import Stellmacher.CharacteristicTwoNormal
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The normal supplement in Stellmacher (8.3)

Assuming the 2-core of the initial residual lies in the next vertex core,
there is a native member of the local family for their join which generates
the initial vertex stabilizer together with the specified edge Sylow group.
All vertices belong to the actual critical path in the supplied local context.
Only its Section Seven hypotheses enter this argument; the old ambient-context
interfaces remain exact wrappers through the graph-preserving local adapter.
The centrality assumption of (8.3) is not needed for this initial step.
The normal-supplement companion retains its exact Sylow image, local-family
eligibility and generating equation for the subsequent native module bound.

Modulo the initial 2-core, (3.3) makes the residual an odd-prime group. Its
intersection with the edge Sylow therefore has trivial quotient image and
lies in the residual 2-core. The residual joined with the next core is
normal in the initial stabilizer, and normal Sylow intersection gives the
next core as its exact Sylow image. Characteristic-two inheritance proves
the supplement has nontrivial 2-core; (7.6) excludes the degenerate case in
which that core is its whole Sylow subgroup. The normal-supplement form of
(3.2) and (3.3) then selects the generating local-family member.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.3), journal p.38;
refs/latex/stellmacher-n-group.tex, its opening family-selection argument.
-/

open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
open Stellmacher.SectionThree CosetGraphContext
namespace Stellmacher.SectionEight
private theorem residual_inter_sylow_le_core
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (h : SectionThree.Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) :
    twoResidualAmbient P ⊓ S ≤ twoCoreIn (twoResidualAmbient P) := by
  classical
  have hSP : S ≤ P := by
    obtain ⟨T,hT⟩ := hP.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le _
  obtain ⟨B,hB,hSB,huniq⟩ := hP.2
  have h33 := lemma_three_three S h P hP B B.normalCore
    ⟨hB, fun s hs => by
      obtain ⟨b,hb,he⟩ := hSB hs
      exact (P.subtype_injective he) ▸ hb, by
        intro B' hb hs
        apply huniq B' hb
        intro s hS
        exact ⟨⟨s,hSP hS⟩,hs hS,rfl⟩⟩
    ⟨B.normalCore_le,inferInstance,by
      intro N hN hNB
      let _ : N.Normal := hN
      exact Subgroup.normal_le_normalCore.mpr hNB⟩ hsolv
  obtain ⟨p,hp,hodd,hRp⟩ := h33.part_a
  let _ : Fact p.Prime := ⟨hp⟩
  let qP := QuotientGroup.mk' (pCore 2 P)
  let I := (twoResidualAmbient P ⊓ S).subgroupOf P
  have hI2 : IsPGroup 2 I :=
    (h.nontrivial_two_subgroup.2.to_le
      (show twoResidualAmbient P ⊓ S ≤ S from inf_le_right)).comap_of_injective
        P.subtype P.subtype_injective
  have hIp : IsPGroup p (I.map qP) := hRp.to_le (by
    rw [← twoResidualAmbient_subgroupOf_map_quotient P]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono P inf_le_left))
  have hbot : I.map qP = ⊥ :=
    disjoint_self.mp (IsPGroup.disjoint_of_ne 2 p
      (fun he => by subst p; exact (by decide : ¬ Odd (2 : ℕ)) hodd)
      _ _ (hI2.map qP) hIp)
  have hIQ : twoResidualAmbient P ⊓ S ≤ twoCoreIn P := by
    intro x hx
    let xp : P := ⟨x, (Subgroup.map_subtype_le _ : twoResidualAmbient P ≤ P) hx.1⟩
    have hmem : qP xp ∈ I.map qP := Subgroup.mem_map_of_mem qP hx
    rw [hbot] at hmem
    exact Subgroup.mem_map_of_mem P.subtype
      ((QuotientGroup.eq_one_iff (N := pCore 2 P) xp).mp hmem)
  rw [show twoResidualAmbient P = twoResidualIn P from rfl,
    SevenSix.residual_core_eq_inter_core]
  exact le_inf inf_le_left hIQ

private theorem sylow_in_normal_supplement
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (E T L : Subgroup G) [E.Normal] [L.Normal]
    (hTS : T ≤ (S : Subgroup G)) (hL : L = E ⊔ T)
    (hSE : (S : Subgroup G) ⊓ E ≤ T) :
    IsSylowSubgroupIn T L := by
  have hSL : (S : Subgroup G) ⊓ L = T := by
    apply le_antisymm
    · intro s hs
      rw [hL] at hs
      obtain ⟨e, he, t, ht, het⟩ := Subgroup.mem_sup_of_normal_left.mp hs.2
      have heS : e ∈ (S : Subgroup G) := by
        have heq : e = s * t⁻¹ := by rw [← het]; group
        rw [heq]
        exact (S : Subgroup G).mul_mem hs.1 ((S : Subgroup G).inv_mem (hTS ht))
      rw [← het]
      exact T.mul_mem (hSE ⟨heS, he⟩) ht
    · exact le_inf hTS (by rw [hL]; exact le_sup_right)
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal L
  refine ⟨U, ?_⟩
  rw [hU, Subgroup.subgroupOf_map_subtype, hSL]

private theorem sylow_in_normal_supplement_ambient
    {G : Type*} [Group G] [Finite G]
    (S E T L P : Subgroup G) (hSP : IsSylowTwoIn S P)
    (hEP : E ≤ P) (hLP : L ≤ P)
    (hEN : (E.subgroupOf P).Normal) (hLN : (L.subgroupOf P).Normal)
    (hTS : T ≤ S) (hL : L = E ⊔ T) (hSE : S ⊓ E ≤ T) :
    IsSylowSubgroupIn T L := by
  let _ : (E.subgroupOf P).Normal := hEN
  let _ : (L.subgroupOf P).Normal := hLN
  obtain ⟨hSPle, U,hU⟩ := hSP
  have hUP : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSPle]
    exact hU
  have hTP := hTS.trans hSPle
  have hLP' : L.subgroupOf P = E.subgroupOf P ⊔ T.subgroupOf P := by
    rw [hL,Subgroup.subgroupOf_sup hEP hTP]
  obtain ⟨V,hV⟩ := sylow_in_normal_supplement U
    (E.subgroupOf P) (T.subgroupOf P) (L.subgroupOf P)
    (by rw [hUP]; exact Subgroup.subgroupOf_mono P hTS) hLP'
    (by rw [hUP]; intro x hx; exact hSE hx)
  let e : L.subgroupOf P ≃* L := Subgroup.subgroupOfEquivOfLe hLP
  let W : Sylow 2 L := V.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨W, ?_⟩
  have hm := congrArg (fun A : Subgroup P => A.map P.subtype) hV
  rw [Subgroup.map_subgroupOf_eq_of_le hTP,Subgroup.map_map] at hm
  change ((V : Subgroup (L.subgroupOf P)).map e.toMonoidHom).map L.subtype = T
  rw [Subgroup.map_map]
  exact hm

private theorem normal_twoCore_le
    {G : Type*} [Group G] (L P : Subgroup G)
    (hLP : L ≤ P) (hLN : (L.subgroupOf P).Normal) :
    twoCoreIn L ≤ twoCoreIn P := by
  have hcP := (SevenSix.twoCoreIn_le L).trans hLP
  have hcN := SevenSix.twoCoreIn_normal_of_normal L P hLP hLN
  have hc2 : IsPGroup 2 ((twoCoreIn L).subgroupOf P) :=
    ((pCore_isPGroup (p := 2) (G := L)).map L.subtype).comap_of_injective
      P.subtype P.subtype_injective
  rw [← Subgroup.map_subgroupOf_eq_of_le hcP]
  exact Subgroup.map_mono (show (twoCoreIn L).subgroupOf P ≤ pCore 2 P from
    le_sSup ⟨hcN,hc2⟩)

private theorem normal_twoCore_ne_bot
    {G : Type*} [Group G] [Finite G] (L P : Subgroup G)
    (hLP : L ≤ P) (hLN : (L.subgroupOf P).Normal)
    (hsolv : Group.IsSolvable P) (hchar : IsCharacteristicTwoType P)
    (hLne : L ≠ ⊥) : twoCoreIn L ≠ ⊥ := by
  let _ : (L.subgroupOf P).Normal := hLN
  have hc := characteristicTwo_normal_subgroup hsolv hchar (L.subgroupOf P)
  let e : L.subgroupOf P ≃* L := Subgroup.subgroupOfEquivOfLe hLP
  intro hbot
  have hcore : pCore 2 L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hbot
  have hcoreI : pCore 2 (L.subgroupOf P) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso 2 e,hcore]
  have htop : (⊤ : Subgroup (L.subgroupOf P)) ≤ ⊥ := by
    change Subgroup.centralizer (pCore 2 (L.subgroupOf P) : Set (L.subgroupOf P)) ≤
      pCore 2 (L.subgroupOf P) at hc
    rw [hcoreI] at hc
    intro x _
    apply hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]
  apply hLne
  apply le_bot_iff.mp
  intro x hx
  have he := htop (Subgroup.mem_top (e.symm ⟨x,hx⟩))
  have hxe : e (e.symm ⟨x,hx⟩) = 1 := by simpa using congrArg e he
  exact congrArg Subtype.val ((e.apply_symm_apply ⟨x,hx⟩).symm.trans hxe)

/-- The normal supplement and its exact next-core Sylow image in (8.3). -/
public theorem eight_three_normal_supplement_local
    {H : Type*} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcontained : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.firstStep) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    L ∈ LSet (⊤ : Subgroup H) (QAt ctx.Γ ctx.criticalPath.firstStep) ∧
      NormalIn L (GAt ctx.Γ ctx.criticalPath.a) ∧
      L ⊔ S = GAt ctx.Γ ctx.criticalPath.a ∧
      ¬ QAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.a := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let E := e Γ cp.a
  let T := q Γ cp.firstStep
  let L := E ⊔ T
  have hEP : E ≤ P := by
    rw [show E = twoResidualIn P from Γ.twoResidualAt_def cp.a]
    exact SevenSix.twoResidualIn_le P
  have hEN : (E.subgroupOf P).Normal := by
    rw [show E = twoResidualIn P from Γ.twoResidualAt_def cp.a]
    exact SevenSix.twoResidualIn_normal P
  have hTS : T ≤ S := (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hSP := (SevenSix.edge_sylow_data h Γ cp).1
  have hTP : T ≤ P := hTS.trans hSP.1
  have hLP : L ≤ P := sup_le hEP hTP
  have hPN : P ≤ Subgroup.normalizer (E : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp hEN
  have hST : S ≤ Subgroup.normalizer (T : Set H) :=
    (SevenSix.edge_sylow_data h Γ cp).2.1.trans (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep)
  have hSN : S ≤ Subgroup.normalizer (L : Set H) :=
    (le_inf (hSP.1.trans hPN) hST).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup E T)
  have hES : E ⊔ S = P := by
    rw [show E = twoResidualIn P from Γ.twoResidualAt_def cp.a]
    exact SevenSix.twoResidualIn_sup_sylow hSP
  have hLN : (L.subgroupOf P).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hLP).mpr
    rw [← hES]
    exact sup_le (le_sup_left.trans L.le_normalizer) hSN
  have hP := (pFamily_iff_pSet _ _ _).mp (SevenSix.edge_local_data h Γ cp).1.1
  have hsolv := (SevenSix.edge_local_data h Γ cp).1.2
  have hSE : S ⊓ E ≤ T := by
    rw [inf_comm]
    have hi := residual_inter_sylow_le_core S (SevenSix.sectionThreeHypotheses h) P hP hsolv
    rw [← show E = twoResidualAmbient P from Γ.twoResidualAt_def cp.a] at hi
    exact hi.trans hcontained
  have hSyl : IsSylowSubgroupIn T L :=
    sylow_in_normal_supplement_ambient S E T L P hSP hEP hLP hEN hLN hTS rfl hSE
  have hTnot : ¬ T ≤ twoCoreIn P := by
    intro ht
    apply (lemma_seven_six h Γ cp).next_residual_core.1
    have hi : twoCoreIn (e Γ cp.firstStep) ≤ T := by
      change twoCoreIn (e Γ cp.firstStep) ≤ q Γ cp.firstStep
      rw [q, Γ.twoCoreAt_def]
      rw [show e Γ cp.firstStep = twoResidualIn (stabilizer Γ cp.firstStep) from Γ.twoResidualAt_def cp.firstStep,
        SevenSix.residual_core_eq_inter_core]
      exact inf_le_right
    rw [q, Γ.twoCoreAt_def]
    exact hi.trans ht
  have hcoreLP := normal_twoCore_le L P hLP hLN
  have hLne : L ≠ ⊥ := by
    intro hb
    apply hTnot
    exact (show T ≤ L from le_sup_right).trans (hb ▸ bot_le)
  have hcoreLne := normal_twoCore_ne_bot L P hLP hLN hsolv
    (SevenSix.edge_characteristic_data h Γ cp).1 hLne
  have hLset : L ∈ LSet (⊤ : Subgroup H) T :=
    ⟨le_top,hSyl,hcoreLne,fun he => hTnot (he ▸ hcoreLP)⟩
  refine ⟨hLset, ⟨hLP,hLN⟩, le_antisymm (sup_le hLP hSP.1)
    (hES.ge.trans (sup_le_sup_right le_sup_left S)), ?_⟩
  change ¬ T ≤ q Γ cp.a
  rw [q, Γ.twoCoreAt_def]
  exact hTnot

/-- The local family member used in the opening of Stellmacher (8.3). -/
public theorem eight_three_local_family_local
    {H : Type*} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcontained : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ F : Subgroup H,
      F ∈ PSet (EAt ctx.Γ ctx.criticalPath.a ⊔
        QAt ctx.Γ ctx.criticalPath.firstStep) (QAt ctx.Γ ctx.criticalPath.firstStep) ∧
      F ⊔ S = GAt ctx.Γ ctx.criticalPath.a := by
  let h := ctx.sectionSeven
  obtain ⟨hL,hnormal,_hgen,hnot⟩ := eight_three_normal_supplement_local ctx hcontained
  apply exists_pSet_generating_of_normal_supplement S (SevenSix.sectionThreeHypotheses h)
    (GAt ctx.Γ ctx.criticalPath.a)
    ((pFamily_iff_pSet _ _ _).mp (SevenSix.edge_local_data h ctx.Γ ctx.criticalPath).1.1)
    (SevenSix.edge_local_data h ctx.Γ ctx.criticalPath).1.2
    (QAt ctx.Γ ctx.criticalPath.firstStep) _
    (SevenSix.local_cores_le_edge_sylow h ctx.Γ ctx.criticalPath).2 hL
    hnormal.1 hnormal.2
  change ¬ QAt ctx.Γ ctx.criticalPath.firstStep ≤ q ctx.Γ ctx.criticalPath.a at hnot
  rw [q, ctx.Γ.twoCoreAt_def] at hnot
  exact hnot

/-- The ambient-context interface, via the graph-preserving local adapter. -/
public theorem eight_three_normal_supplement
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcontained : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.firstStep) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    L ∈ LSet (⊤ : Subgroup H) (QAt ctx.Γ ctx.criticalPath.firstStep) ∧
      NormalIn L (GAt ctx.Γ ctx.criticalPath.a) ∧
      L ⊔ S = GAt ctx.Γ ctx.criticalPath.a ∧
      ¬ QAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.a := by
  exact eight_three_normal_supplement_local ctx.toLocalContext hcontained

/-- The ambient-context interface, via the graph-preserving local adapter. -/
public theorem eight_three_local_family
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcontained : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ F : Subgroup H,
      F ∈ PSet (EAt ctx.Γ ctx.criticalPath.a ⊔
        QAt ctx.Γ ctx.criticalPath.firstStep) (QAt ctx.Γ ctx.criticalPath.firstStep) ∧
      F ⊔ S = GAt ctx.Γ ctx.criticalPath.a := by
  exact eight_three_local_family_local ctx.toLocalContext hcontained

end Stellmacher.SectionEight
