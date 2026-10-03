module
public import Stellmacher.SectionEight.EightFourLengthTwoFullCenterCommutator
public import Stellmacher.SectionEight.EightFourRelativeNormalStarCoreCentralization
public import Stellmacher.SectionFiveToSeven.EdgeSylowGeneration
public import Stellmacher.SectionFiveToSeven.LocalResidualCoreContainment
/-!
# The chosen length-two star centralizes the terminal residual core

For the same endpoint actor and star family in source (8) of (8.4), assume
the two neighbor modules contain the endpoint residual and the initial
center together with the selected new edge generates the endpoint stabilizer.
If the selected star lies in the original first-step core, it centralizes
the two-core of the endpoint residual.

The full-center commutator theorem puts [Cm,Za] in Zend. Normality of Cm
in its own vertex stabilizer and of Zend in the endpoint stabilizer makes
Cm Zend normalized by the entire new edge. The supplied same-actor edge
generation therefore makes this join normal in the endpoint stabilizer.
Unique maximality replaces full edges by their actual Sylow two-subgroups.
These supply two generating supplements: one to Za and one to the selected
neighbor module, the latter from the residual-containing pair of modules.
The local odd residual quotient and core containment give the precise
hypotheses of the relative normal-star three-subgroup theorem.

No full edge is assumed to be a two-group, and the endpoint core is not
assumed contained in the original edge Sylow. All actors, stars, residuals
and subgroup quotients are the actual ones of the original context.
The local theorem uses the same actual graph and witness in canonical and
generated contexts; the original canonical theorem is an exact wrapper.
Source: Stellmacher, Journal of Algebra 190 (1997), (8.4)(8), printed p.39.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement
universe u

public theorem eight_four_length_two_residual_centralization_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
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
    (C : ctx.Γ.Vertex → Subgroup H)
    (hC : ∀ g d, C (ctx.Γ.act g d) = (C d).conjBy g⁻¹)
    (hbase : C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype)
    (hCV : ∀ d, C d ≤ VAt ctx.Γ d)
    (hCn : ∀ d, NormalIn (C d) (GAt ctx.Γ d))
    (hlen : ctx.criticalPath.length = 2) (g : H)
    (hg : g ∈ GAt ctx.Γ ctx.criticalPath.a')
    (hgen : EAt ctx.Γ ctx.criticalPath.a' ≤
      VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep))
    (hcore : C (ctx.Γ.act g ctx.criticalPath.firstStep) ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hedgegen : ZAt ctx.Γ ctx.criticalPath.a ⊔
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) =
      GAt ctx.Γ ctx.criticalPath.a') :
    ⁅C (ctx.Γ.act g ctx.criticalPath.firstStep),twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let m := Γ.act g cp.firstStep
  let P := GAt Γ cp.a'
  let M := C m
  let Z := ZAt Γ cp.a'
  let A := ZAt Γ cp.a
  let B := VAt Γ m
  let edge := P ⊓ GAt Γ m
  let oldedge := P ⊓ GAt Γ cp.firstStep
  have hb : cp.length = 2 := hlen
  have hadj : Γ.adjacent cp.a' cp.firstStep := by
    have he := cp.path_adj ⟨1,by omega⟩
    have hi : (⟨1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    change Γ.adjacent (cp.path ⟨1,by omega⟩) cp.a' at he
    rw [cp.path_first] at he
    exact Γ.adjacent_symm he
  have hfix : Γ.act g cp.a' = cp.a' :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.a') g).mp hg
  have hm : Γ.adjacent cp.a' m := by simpa only [hfix] using adjacent_act Γ g hadj
  have hn := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hm
  have hnold := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj
  have hCQ : C cp.firstStep ≤ q Γ cp.a' :=
    hbase.le.trans (eight_four_fixed_closure_control_local ctx hcenter w hbranch).1
  have hMQ : M ≤ q Γ cp.a' := by
    have hh := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hCQ
    change (C cp.firstStep).conjBy g⁻¹ ≤ (q Γ cp.a').conjBy g⁻¹ at hh
    rw [← hC g cp.firstStep] at hh
    have hq := SevenSix.q_act Γ g cp.a'
    rw [hfix] at hq
    exact hh.trans_eq hq.symm
  have hQP : q Γ cp.a' ≤ P := by rw [q,Γ.twoCoreAt_def]; exact Subgroup.map_subtype_le _
  have hMP : M ≤ P := hMQ.trans hQP
  have hZP : Z ≤ P :=
    ((lemma_seven_three h Γ).center_core cp.a' m hn).trans
      ((Subgroup.map_subtype_le _).trans hQP)
  have hAP : A ≤ P :=
    ((lemma_seven_four h Γ cp).first_containment.1.trans (lemma_seven_four h Γ cp).first_containment.2)
  have hBP : B ≤ P :=
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) m).trans
      ((lemma_seven_three h Γ).sylow_and_core m cp.a'
        ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hm)) default).2.2
  have hZn : NormalIn Z P :=
    (edge_sectionThree_data h Γ
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hm)) default).2.2.2.2.2
  have hMA : ⁅M,A⁆ ≤ Z :=
    eight_four_length_two_full_center_commutator_local ctx hcenter w hbranch C hC hbase hCV hCn hlen g hg hgen hcore
  have hMB : ⁅M,B⁆ = ⊥ :=
    eight_four_length_two_star_centralizes_module_local ctx hcenter w hbranch C hC hbase hCV hlen g
  have hMZn : NormalIn (M ⊔ Z) P := by
    have hMZP : M ⊔ Z ≤ P := sup_le hMP hZP
    apply And.intro hMZP
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hMZP).mpr
    have hAn : A ≤ Subgroup.normalizer ((M ⊔ Z : Subgroup H) : Set H) := by
      let _ : (Z.subgroupOf P).Normal := hZn.2
      have hsup : (M ⊔ Z).subgroupOf P = M.subgroupOf P ⊔ Z.subgroupOf P := by
        apply Subgroup.map_injective P.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le hMZP,Subgroup.map_sup,
          Subgroup.map_subgroupOf_eq_of_le hMP,Subgroup.map_subgroupOf_eq_of_le hZP]
      have hcomm : ⁅M.subgroupOf P,A.subgroupOf P⁆ ≤ Z.subgroupOf P := by
        intro t ht
        have hh := Subgroup.mem_map_of_mem P.subtype ht
        rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hMP,
          Subgroup.map_subgroupOf_eq_of_le hAP] at hh
        exact hMA hh
      have hn := Subgroup.le_normalizer_sup_of_commutator_le
        (M.subgroupOf P) (A.subgroupOf P) (M.subgroupOf P) (Z.subgroupOf P) le_rfl hcomm
      apply Subgroup.le_normalizer_iff.mpr
      intro a ha t ht
      have htn : (⟨t,hMZP ht⟩ : P) ∈ M.subgroupOf P ⊔ Z.subgroupOf P := hsup ▸ ht
      have hr := (Subgroup.mem_normalizer_iff.mp (hn (show (⟨a,hAP ha⟩ : P) ∈ A.subgroupOf P from ha)) _).mp htn
      rw [← hsup] at hr
      exact hr
    have hedgen : edge ≤ Subgroup.normalizer ((M ⊔ Z : Subgroup H) : Set H) :=
      (le_inf (inf_le_right.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (hCn m).1).mp (hCn m).2))
        (inf_le_left.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mp hZn.2))).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup M Z)
    have he : A ⊔ edge = P := hedgegen
    exact he ▸ sup_le hAn hedgen
  let t : Sylow 2 edge := default
  let u : Sylow 2 oldedge := default
  let T := sylowTwoAmbient edge t
  let U := sylowTwoAmbient oldedge u
  have hT : IsPGroup 2 T := t.isPGroup'.map edge.subtype
  have hU : IsPGroup 2 U := u.isPGroup'.map oldedge.subtype
  have hAT : A ⊔ T = P := edge_sylow_generation h Γ cp.a' m hm A hedgegen t
  have hUP : U ≤ P := (Subgroup.map_subtype_le _).trans inf_le_left
  have hUold := ((lemma_seven_three h Γ).sylow_and_core cp.a' cp.firstStep hnold u).1
  have holdgen : B ⊔ oldedge = P := by
    have hVedge : VAt Γ cp.firstStep ≤ oldedge := le_inf
      ((SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) cp.firstStep).trans
        ((lemma_seven_three h Γ).sylow_and_core cp.firstStep cp.a'
          ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hadj)) default).2.2)
      ((SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) cp.firstStep).trans
        (by rw [q,Γ.twoCoreAt_def]; exact Subgroup.map_subtype_le _))
    have hres : EAt Γ cp.a' ≤ B ⊔ oldedge := hgen.trans (sup_le
      (hVedge.trans le_sup_right) le_sup_left)
    have hsupp : EAt Γ cp.a' ⊔ U = P := by
      rw [show EAt Γ cp.a' = twoResidualAmbient P from Γ.twoResidualAt_def cp.a']
      exact SectionThree.twoResidual_sup_sylowImage hUold.2
    apply le_antisymm (sup_le hBP inf_le_left)
    exact hsupp.ge.trans (sup_le hres ((Subgroup.map_subtype_le _).trans le_sup_right))
  have hBU : B ⊔ U = P := edge_sylow_generation h Γ cp.a' cp.firstStep hadj B holdgen u
  have hQcore : twoCoreIn (twoResidualIn P) ≤ q Γ cp.a' :=
    local_residual_core_le_vertex_core h Γ cp.a' m hn P le_rfl
  have hQM : twoCoreIn (twoResidualIn P) ≤ Subgroup.normalizer M := hQcore.trans
    (((lemma_seven_three h Γ).sylow_and_core cp.a' m hn t).2.2.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hCn m).1).mp (hCn m).2))
  have hZQ : ⁅Z,twoCoreIn (twoResidualIn P)⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact (((lemma_seven_three h Γ).center_core cp.a' m hn).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))).trans
          (Subgroup.centralizer_le hQcore)
  have hodd := local_residual_core_quotient_odd h Γ cp.a' m hn P le_rfl
  have hh := eight_four_relative_normal_star_core_centralization P M Z A B T U
    hMP hZP hZn.2 hMZn.2 hAT hBU hT hU hMA hMB hQM hZQ hodd
  change ⁅M,twoCoreIn (EAt Γ cp.a')⁆ = ⊥
  have he : EAt Γ cp.a' = twoResidualIn P := Γ.twoResidualAt_def cp.a'
  rwa [he]
public theorem eight_four_length_two_residual_centralization
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
    (C : ctx.Γ.Vertex → Subgroup H)
    (hC : ∀ g d, C (ctx.Γ.act g d) = (C d).conjBy g⁻¹)
    (hbase : C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype)
    (hCV : ∀ d, C d ≤ VAt ctx.Γ d)
    (hCn : ∀ d, NormalIn (C d) (GAt ctx.Γ d))
    (hlen : ctx.criticalPath.length = 2) (g : H)
    (hg : g ∈ GAt ctx.Γ ctx.criticalPath.a')
    (hgen : EAt ctx.Γ ctx.criticalPath.a' ≤
      VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep))
    (hcore : C (ctx.Γ.act g ctx.criticalPath.firstStep) ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hedgegen : ZAt ctx.Γ ctx.criticalPath.a ⊔
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) =
      GAt ctx.Γ ctx.criticalPath.a') :
    ⁅C (ctx.Γ.act g ctx.criticalPath.firstStep),twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆ = ⊥  := by
  exact eight_four_length_two_residual_centralization_local ctx.toLocalContext hcenter w hbranch C hC hbase hCV hCn hlen g hg hgen hcore hedgegen

end Stellmacher.SectionEight
