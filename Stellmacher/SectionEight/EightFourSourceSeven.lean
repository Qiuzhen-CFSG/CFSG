module
public import Stellmacher.SectionEight.EightFourConjugateClosureCoreCentralization
public import Stellmacher.SectionFiveToSeven.LocalResidualCoreContainment
public import Stellmacher.SectionEight.EightFourStarFixedCentralization
public import Stellmacher.SectionEight.EightFourStarNeighborModule
public import Stellmacher.SectionEight.EightFourEdgeStarClosure
public import Stellmacher.SectionEight.EightFourTransportedCentralizerCriterion

/-!
# The actual edge-fixed subgroup implication in source (7)

In the local context carrying the proved ambient vector criterion, retain
the exact critical path, faithful quotient witness, and equivariant
edge-fixed family in the central-first-step, nontrivial-closure branch of
Stellmacher (8.4). The first configuration supplies A,L0,x and the transported
predecessor d. The second configuration supplies a neighbor next2 and a
subgroup Ltilde generating G_d with the full edge, in either of its actual
star/core alternatives. If D lies in F(next2,d) and [D,A] lies in the endpoint
center, then D lies in Z_d.

The star-fixed theorem makes D centralize the initial star. The exact local
residual-core and odd-quotient facts, transported into the terminal stabilizer,
let the conjugate-closure argument make D centralize the selected residual
core as well. Since F(next2,d) lies in Z_next2, D centralizes Q_next2. Thus it
centralizes Ltilde in either second-configuration case. Full-edge generation
then meets the transported vector-centralizer criterion for each element of
D, using the original witness and edge family. Pure graph consequences use
the underlying local context; the final vector step uses its actual ambient
callback. The original canonical statement remains an exact wrapper.

The private subtype transfer carries the residual, its two-core and its odd
quotient through actual equivalences. It requires normality only inside the
terminal stabilizer and does not place D inside L0 or its core supplement.
The source6 cardinality and further containment clauses are not needed for
this implication; its generator equalities are retained. Source: Stellmacher
(8.4)(7), Journal of Algebra190 (1997), printed p39, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem relative_conjugate_closure_core_centralization
    {G : Type*} [Group G] [Finite G]
    (P D Y Z A T L : Subgroup G)
    (hDP : D ≤ P) (hYP : Y ≤ P) (hZP : Z ≤ P) (hTP : T ≤ P) (hLP : L ≤ P)
    (hZn : (Z.subgroupOf P).Normal) (hTn : (T.subgroupOf P).Normal)
    (x : G) (hgen : (A ⊔ A.conjBy x) ⊔ T = L) (hx : x ∈ A ⊔ A.conjBy x)
    (hT : IsPGroup 2 T) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hZT : ⁅Z,T⁆ = ⊥) (hYA : ⁅Y,A.conjBy x⁆ = ⊥)
    (hDY : D ≤ Y) (hDA : ⁅D,A⁆ ≤ Z)
    (hQT : twoCoreIn (twoResidualIn L) ≤ T)
    (hodd : Odd (Nat.card (twoResidualIn L ⧸ pCore 2 (twoResidualIn L)))) :
    ⁅D,twoCoreIn (twoResidualIn L)⁆ = ⊥ := by
  let LP := L.subgroupOf P
  let RP := twoResidualAmbient LP
  let R := twoResidualIn L
  have hmapR : RP.map P.subtype = R :=
    map_twoResidualAmbient_of_subgroup_image LP P.subtype L
      (Subgroup.map_subgroupOf_eq_of_le hLP)
  let eR : RP ≃* R := (RP.equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr hmapR)
  have hcomp : R.subtype.comp eR.toMonoidHom = P.subtype.comp RP.subtype := by ext r; rfl
  have hcores : (pCore 2 RP).map eR.toMonoidHom = pCore 2 R := pCore_map_iso 2 eR
  have hmapQ : (twoCoreIn RP).map P.subtype = twoCoreIn R := by
    unfold twoCoreIn
    rw [← hcores,Subgroup.map_map,Subgroup.map_map,hcomp]
  have hoddP : Odd (Nat.card (RP ⧸ pCore 2 RP)) := by
    rw [Nat.card_congr (QuotientGroup.congr (pCore 2 RP) (pCore 2 R) eR hcores).toEquiv]
    exact hodd
  have hAP : A ≤ P := (le_sup_left.trans (le_sup_left.trans_eq hgen)).trans hLP
  have hAxP : A.conjBy x ≤ P := (le_sup_right.trans (le_sup_left.trans_eq hgen)).trans hLP
  have hxP : x ∈ P := ((le_sup_left.trans_eq hgen).trans hLP) hx
  let xP : P := ⟨x,hxP⟩
  have hconj : (A.subgroupOf P).conjBy xP = (A.conjBy x).subgroupOf P := by
    ext a
    simp only [Subgroup.conjBy,Subgroup.mem_map_equiv,Subgroup.mem_subgroupOf]
    rfl
  let _ : (Z.subgroupOf P).Normal := hZn
  let _ : (T.subgroupOf P).Normal := hTn
  have hgenP : (A.subgroupOf P ⊔ (A.subgroupOf P).conjBy xP) ⊔ T.subgroupOf P = LP := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hconj,Subgroup.map_sup,Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hAP,Subgroup.map_subgroupOf_eq_of_le hAxP,
      Subgroup.map_subgroupOf_eq_of_le hTP,Subgroup.map_subgroupOf_eq_of_le hLP]
    exact hgen
  have hxgen : xP ∈ A.subgroupOf P ⊔ (A.subgroupOf P).conjBy xP := by
    apply (Subgroup.mem_map_iff_mem P.subtype_injective).mp
    rw [hconj,Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hAP,
      Subgroup.map_subgroupOf_eq_of_le hAxP]
    exact hx
  have hTYP : T.subgroupOf P ≤ Subgroup.normalizer (Y.subgroupOf P : Set P) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro t ht y hy
    exact (Subgroup.mem_normalizer_iff.mp (hTY ht) (y : G)).mp hy
  have hZTP : ⁅Z.subgroupOf P,T.subgroupOf P⁆ = ⊥ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hZP,
      Subgroup.map_subgroupOf_eq_of_le hTP,Subgroup.map_bot,hZT]
  have hYAP : ⁅Y.subgroupOf P,(A.subgroupOf P).conjBy xP⁆ = ⊥ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hconj,Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hYP,
      Subgroup.map_subgroupOf_eq_of_le hAxP,Subgroup.map_bot,hYA]
  have hDAP : ⁅D.subgroupOf P,A.subgroupOf P⁆ ≤ Z.subgroupOf P := by
    intro t ht
    have hm := Subgroup.mem_map_of_mem P.subtype ht
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hDP,
      Subgroup.map_subgroupOf_eq_of_le hAP] at hm
    exact hDA hm
  have hQTP : twoCoreIn RP ≤ T.subgroupOf P := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [hmapQ,Subgroup.map_subgroupOf_eq_of_le hTP]
    exact hQT
  have hresult := eight_four_conjugate_closure_core_centralization
    (D.subgroupOf P) (Y.subgroupOf P) (Z.subgroupOf P) (A.subgroupOf P)
    (T.subgroupOf P) LP xP hgenP hxgen hT.comap_subtype hTYP hZTP hYAP
    (fun _ hd => hDY hd) hDAP hQTP hoddP
  have hm := congrArg (Subgroup.map P.subtype) hresult
  rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hDP,Subgroup.map_bot] at hm
  change ⁅D,(twoCoreIn RP).map P.subtype⁆ = ⊥ at hm
  rw [hmapQ] at hm
  exact hm



/-- Source (7): an edge-fixed subgroup with the prescribed actor commutator lies in the new center. -/
public theorem eight_four_source_seven_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (A L0 : Subgroup H) (x : H)
    (hA : A ≤ ZAt ctx.Γ ctx.criticalPath.a)
    (hL0 : L0 ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hLgen : L0 = A ⊔ A.conjBy x) (hx : x ∈ L0)
    (d next2 : ctx.Γ.Vertex)
    (hd : d = ctx.Γ.act x⁻¹ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,by omega⟩))
    (hadj : ctx.Γ.adjacent d next2)
    (Ltilde : Subgroup H)
    (hfull : Ltilde ⊔ (GAt ctx.Γ d ⊓ GAt ctx.Γ next2) = GAt ctx.Γ d)
    (hcase : Ltilde = (⨆ k, F k ctx.criticalPath.firstStep) ⊔ QAt ctx.Γ next2 ∨
      Ltilde = twoCoreIn (twoResidualIn (L0 ⊔ QAt ctx.Γ ctx.criticalPath.a')) ⊔
        QAt ctx.Γ next2)
    (D : Subgroup H) (hD : D ≤ F next2 d)
    (hDA : ⁅D,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') :
    D ≤ ZAt ctx.Γ d := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let C : Γ.Vertex → Subgroup H := fun l => ⨆ k, F k l
  let prev := cp.path ⟨cp.length-1,by omega⟩
  let P := GAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let T := QAt Γ cp.a'
  let L := L0 ⊔ T
  obtain ⟨hCb,hCc,hFC,hCn⟩ := eight_four_edge_star_closure_local ctx.toLocalContext w F hbase hcov hsub hformula
  have hCV : ∀ l, C l ≤ VAt Γ l := eight_four_star_le_neighbor_module_local ctx.toLocalContext w F hsub hformula
  have hDC : D ≤ C d := hD.trans (hFC next2 d)
  have hDstar : ⁅D,C cp.firstStep⁆ = ⊥ := by
    apply eight_four_star_fixed_centralization_local ctx.toLocalContext hcenter w hbranch C hCc hCb hCV A L0 D x
      hA hL0 hLgen hx
    · simpa only [hd, EightFourLocalContext.toLocalContext] using hDC
    · exact hDA
  have hpos := cp.length_pos
  have hprevadj : Γ.adjacent cp.a' prev := by
    have he := cp.path_adj ⟨cp.length-1,by omega⟩
    have hi : (⟨cp.length-1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    exact Γ.adjacent_symm he
  have hprev := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hprevadj
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hxP : x ∈ P := hL0 hx
  have hfix : Γ.act x⁻¹ cp.a' = cp.a' := by
    have hh := P.inv_mem hxP
    change x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hh
    rw [Γ.stabilizer_def] at hh
    exact hh
  have hdadj : Γ.adjacent cp.a' d := by
    have hh := adjacent_act Γ x⁻¹ hprevadj
    rwa [hfix,← hd] at hh
  have hdend := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hdadj
  have hendd := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hdadj)
  have hTd : T ≤ GAt Γ d := ((lemma_seven_three h Γ).sylow_and_core cp.a' d hdend default).2.2
  have hTP : T ≤ P := by rw [show T = twoCoreIn P from Γ.twoCoreAt_def cp.a']; exact Subgroup.map_subtype_le _
  have hTn : (T.subgroupOf P).Normal := by
    rw [show T = twoCoreIn P from Γ.twoCoreAt_def cp.a']
    change ((pCore 2 P).map P.subtype |>.comap P.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
    infer_instance
  have hZP : Z ≤ P := ((lemma_seven_three h Γ).center_core cp.a' prev hprev).trans
    ((Subgroup.map_subtype_le _).trans hTP)
  have hZn : (Z.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr (stabilizer_le_normalizer_z Γ cp.a')
  have hYP : C d ≤ P := (hCV d).trans
    ((SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
      (eight_four_centered_length_gt_one_local ctx.toLocalContext hcenter) d).trans
      ((lemma_seven_three h Γ).sylow_and_core d cp.a' hendd default).2.2)
  have hTY : T ≤ Subgroup.normalizer (C d : Set H) := hTd.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (hCn d).1).mp (hCn d).2)
  have hZT : ⁅Z,T⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (((lemma_seven_three h Γ).center_core cp.a' prev hprev).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (SevenSix.centerAmbient_le_centralizer _)))
  have hprevCore : C prev ≤ QAt Γ cp.a :=
    eight_four_predecessor_star_le_initial_core_local ctx.toLocalContext hcenter w hbranch C hCc hCb
  have hQaA : QAt Γ cp.a ≤ Subgroup.centralizer (A : Set H) := by
    apply Subgroup.le_centralizer_iff.mpr
    exact hA.trans (((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (SevenSix.centerAmbient_le_centralizer _)))
  have hprevA : ⁅C prev,A⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hprevCore.trans hQaA)
  have hdEq : C d = (C prev).conjBy x := by
    rw [hd]
    simpa only [inv_inv, EightFourLocalContext.toLocalContext] using hCc x⁻¹ prev
  have hYA : ⁅C d,A.conjBy x⁆ = ⊥ := by
    have hm := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hprevA
    rw [Subgroup.map_commutator,Subgroup.map_bot] at hm
    rw [hdEq]
    exact hm
  have hLp : L ≤ P := sup_le hL0 hTP
  have hDcore : ⁅D,twoCoreIn (twoResidualIn L)⁆ = ⊥ :=
    relative_conjugate_closure_core_centralization P D (C d) Z A T L
      (hDC.trans hYP) hYP hZP hTP hLp hZn hTn x
      (by change (A ⊔ A.conjBy x) ⊔ T = L0 ⊔ T; rw [← hLgen]) (by rwa [← hLgen])
      (by rw [show T = twoCoreIn P from Γ.twoCoreAt_def cp.a']; exact (pCore_isPGroup (p := 2) (G := P)).map P.subtype)
      hTY hZT hYA hDC hDA
      (local_residual_core_le_vertex_core h Γ cp.a' prev hprev L hLp)
      (local_residual_core_quotient_odd h Γ cp.a' prev hprev L hLp)
  have hDQ : ⁅D,QAt Γ next2⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((hD.trans ((hsub next2 d).trans inf_le_left)).trans
        (((lemma_seven_three h Γ).center_core next2 d
          ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hadj))).trans
          ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (SevenSix.centerAmbient_le_centralizer _))))
  have hDL : ⁅D,Ltilde⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rw [Subgroup.le_centralizer_iff]
    rcases hcase with heq | heq
    · rw [heq]
      exact sup_le (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDstar))
        (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDQ))
    · rw [heq]
      exact sup_le (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDcore))
        (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDQ))
  intro v hv
  have hLcent : Ltilde ≤ GAt Γ d ⊓ Subgroup.centralizer ({v} : Set H) := by
    refine le_inf (le_sup_left.trans_eq hfull) ?_
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDL hv) l hl)
  apply eight_four_edge_vector_centralizer_criterion_local ctx hcenter w F hbase hcov hformula next2 d v (hD hv)
  apply le_antisymm (sup_le inf_le_left inf_le_right)
  calc
    GAt Γ d = Ltilde ⊔ (GAt Γ d ⊓ GAt Γ next2) := hfull.symm
    _ ≤ (GAt Γ d ⊓ Subgroup.centralizer ({v} : Set H)) ⊔
        (GAt Γ next2 ⊓ GAt Γ d) := sup_le_sup hLcent (by rw [inf_comm])


/-- Canonical-context wrapper retaining the exact extraction and edge-fixed family. -/
public theorem eight_four_source_seven
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (A L0 : Subgroup H) (x : H)
    (hA : A ≤ ZAt ctx.Γ ctx.criticalPath.a)
    (hL0 : L0 ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hLgen : L0 = A ⊔ A.conjBy x) (hx : x ∈ L0)
    (d next2 : ctx.Γ.Vertex)
    (hd : d = ctx.Γ.act x⁻¹ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,by omega⟩))
    (hadj : ctx.Γ.adjacent d next2)
    (Ltilde : Subgroup H)
    (hfull : Ltilde ⊔ (GAt ctx.Γ d ⊓ GAt ctx.Γ next2) = GAt ctx.Γ d)
    (hcase : Ltilde = (⨆ k, F k ctx.criticalPath.firstStep) ⊔ QAt ctx.Γ next2 ∨
      Ltilde = twoCoreIn (twoResidualIn (L0 ⊔ QAt ctx.Γ ctx.criticalPath.a')) ⊔
        QAt ctx.Γ next2)
    (D : Subgroup H) (hD : D ≤ F next2 d)
    (hDA : ⁅D,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') :
    D ≤ ZAt ctx.Γ d := by
  exact eight_four_source_seven_local
    ctx.toEightFourContext hcenter w hbranch F hbase hcov hsub hformula A L0 x hA hL0 hLgen hx d next2 hd hadj Ltilde hfull hcase D hD hDA

end Stellmacher.SectionEight
