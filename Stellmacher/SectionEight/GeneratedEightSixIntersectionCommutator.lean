module

public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup
public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts
public import Theory.GroupTheory.SylowNormalSupplementIntersection

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement IsMulCommutative

universe u

private theorem sup_commutator_le_of_normalizes
    {G : Type u} [Group G] (P Z U W D : Subgroup G)
    (hnormal : P ≤ Subgroup.normalizer (Z : Set G))
    (hUP : U ≤ P) (hWP : W ≤ P)
    (hU : ⁅U, D⁆ ≤ Z) (hW : ⁅W, D⁆ ≤ Z) : ⁅U ⊔ W, D⁆ ≤ Z := by
  let container : Subgroup G := {
    carrier := {element | element ∈ P ∧ ∀ other ∈ D, ⁅element, other⁆ ∈ Z}
    one_mem' := ⟨P.one_mem, by simp⟩
    mul_mem' := by
      rintro first second ⟨hfirst, hfirstcomm⟩ ⟨hsecond, hsecondcomm⟩
      refine ⟨P.mul_mem hfirst hsecond, ?_⟩
      intro other hother
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact Z.mul_mem
        (Subgroup.le_normalizer_iff.mp hnormal first hfirst _ (hsecondcomm other hother))
        (hfirstcomm other hother)
    inv_mem' := by
      rintro element ⟨helement, hcomm⟩
      refine ⟨P.inv_mem helement, ?_⟩
      intro other hother
      rw [commutatorElement_inv_left]
      have hinv : ⁅other, element⁆ ∈ Z := by
        rw [← commutatorElement_inv]
        exact Z.inv_mem (hcomm other hother)
      simpa only [inv_inv] using Subgroup.le_normalizer_iff.mp hnormal element⁻¹
        (P.inv_mem helement) _ hinv }
  have hUC : U ≤ container := fun element helement =>
    ⟨hUP helement, Subgroup.commutator_le.mp hU element helement⟩
  have hWC : W ≤ container := fun element helement =>
    ⟨hWP helement, Subgroup.commutator_le.mp hW element helement⟩
  exact Subgroup.commutator_le.mpr fun element helement =>
    ((sup_le hUC hWC) helement).2

public theorem eight_six_first_center_le_initial
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep)) :
    ZAt graph path.firstStep ≤ ZAt graph path.a := by
  have hsylow := SevenSix.edge_sylow_data hyp graph path
  have homega (vertex : graph.Vertex) (hs : IsSylowTwoIn S (GAt graph vertex)) :
      omegaOneCenter S ≤ ZAt graph vertex := by
    obtain ⟨_, sylow, hsylow⟩ := hs
    rw [ZAt, z, graph.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  have hcent : omegaOneCenter S ≤ CenterAmbient (GAt graph path.firstStep) :=
    (homega _ hsylow.2).trans hcenter
  have hle : omegaOneCenter S ≤ GAt graph path.firstStep :=
    hcent.trans (Subgroup.map_subtype_le _)
  have hnormal : NormalIn (omegaOneCenter S) (GAt graph path.firstStep) :=
    ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      ((Subgroup.le_centralizer_iff.mp (hcent.trans
        (SevenSix.centerAmbient_le_centralizer _))).trans
          (Subgroup.centralizer_le_normalizer _))⟩
  exact (z_eq_omega_sylow_of_normal graph path.firstStep hsylow.2 hnormal).le.trans
    (homega _ hsylow.1)

public theorem eight_six_intersection_neighbor_commutator_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (data : EightSixEquationOneData graph path previous D L Q)
    (neighbor : graph.Vertex) (hneigh : neighbor ∈ Later.Neighborhood graph path.a) :
    ⁅VAt graph neighbor, D⁆ ≤ ZAt graph path.a := by
  have hfirst : ⁅VAt graph path.firstStep, D⁆ ≤ ZAt graph path.a :=
    ((Subgroup.commutator_mono le_rfl (show D ≤ QAt graph path.firstStep from
      hD ▸ inf_le_right)).trans_eq data.first_commutator).trans
        (eight_six_first_center_le_initial hyp graph path hcenter)
  obtain ⟨actor, hactor⟩ := (lemma_seven_one hyp graph).local_transitivity path.a
    ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj) hneigh
  have hDN : GAt graph path.a ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
      data.intersection_normal.2
  have hDmap : D.map (MulAut.conj (actor : G)⁻¹).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (D : Set G)).inv_mem (hDN actor.property))
  have hZmap : (ZAt graph path.a).map (MulAut.conj (actor : G)⁻¹).toMonoidHom =
      ZAt graph path.a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (ZAt graph path.a : Set G)).inv_mem
        (stabilizer_le_normalizer_z graph path.a actor.property))
  have hmap := Subgroup.map_mono (f := (MulAut.conj (actor : G)⁻¹).toMonoidHom) hfirst
  rw [Subgroup.map_commutator, hDmap, hZmap] at hmap
  rw [← hactor]
  exact (show ⁅v graph (graph.act actor path.firstStep), D⁆ ≤ ZAt graph path.a by
    rw [v_act]; exact hmap)

public theorem eight_six_sylow_intersection_of_residual_le
    {G : Type u} [Group G] [Finite G] (P L S : Subgroup G)
    (hLP : L ≤ P) (hS : IsSylowTwoIn S P) (hresidual : twoResidualIn P ≤ L) :
    IsSylowTwoIn (L ⊓ S) L := by
  obtain ⟨hSP, sylow, hsylow⟩ := hS
  let residual := BenderSuzuki.External.hktPResidual 2 P
  let _ : residual.Normal := BenderSuzuki.External.hktPResidual_normal
  have hresidualMap : residual.map P.subtype = twoResidualIn P := by
    change _ = (twoResidualSubgroup P).map P.subtype
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
  have hgen : residual ⊔ (sylow : Subgroup P) = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, hresidualMap, hsylow, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact SevenSix.twoResidualIn_sup_sylow (show IsSylowTwoIn S P from
      ⟨hSP, sylow, hsylow⟩)
  have hresidualL : residual ≤ L.subgroupOf P := by
    intro element helement
    exact hresidual (hresidualMap ▸ Subgroup.mem_map_of_mem P.subtype helement)
  obtain ⟨inner, hinner⟩ := sylow.exists_map_eq_inf_of_normal_supplement residual
    (L.subgroupOf P) hgen hresidualL
  let equiv := Subgroup.subgroupOfEquivOfLe hLP
  let outer := inner.mapSurjective (f := equiv.toMonoidHom) equiv.surjective
  refine ⟨inf_le_left, outer, ?_⟩
  change ((inner : Subgroup (L.subgroupOf P)).map equiv.toMonoidHom).map L.subtype = _
  have hcomp : L.subtype.comp equiv.toMonoidHom =
      P.subtype.comp (L.subgroupOf P).subtype := rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hinner,
    Subgroup.map_inf _ _ _ P.subtype_injective, hsylow,
    Subgroup.map_subgroupOf_eq_of_le hLP, inf_comm]

public theorem eight_six_intersection_full_commutator_of_frattini
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (previous : graph.Vertex) (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hfrattini : FrattiniAmbient D = ⊥) :
    ⁅D, L⁆ = ZAt graph path.a := by
  let initial := GAt graph path.a
  let center := ZAt graph path.a
  let first := VAt graph path.firstStep
  let oldPart := VAt graph previous ⊓ QAt graph path.a
  let newPart := first ⊓ QAt graph path.a
  have hcore : QAt graph path.a ≤ initial := by
    change graph.twoCoreAt path.a ≤ _
    rw [graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hfirstL : first ≤ L :=
    (le_sup_left.trans data.sylow_intersection.symm.le).trans inf_le_left
  have hQL : Q ≤ L :=
    (le_sup_right.trans data.sylow_intersection.symm.le).trans inf_le_left
  have hDN : D ≤ initial := data.intersection_normal.1
  have hcenterNormal : initial ≤ Subgroup.normalizer (center : Set G) :=
    stabilizer_le_normalizer_z graph path.a
  have hfirstComm : ⁅first, D⁆ ≤ center :=
    eight_six_intersection_neighbor_commutator_le hyp graph path hcenter previous D L Q hD
      data path.firstStep ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj)
  have holdComm : ⁅oldPart, D⁆ ≤ center :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (eight_six_intersection_neighbor_commutator_le hyp graph path hcenter previous D L Q hD
        data previous hprevious)
  have hnewComm : ⁅newPart, D⁆ ≤ center :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans hfirstComm
  have hDp : IsPGroup 2 D := by
    have hfirstCore : IsPGroup 2 (QAt graph path.firstStep) := by
      change IsPGroup 2 (graph.twoCoreAt path.firstStep)
      rw [graph.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := GAt graph path.firstStep)).map
        (GAt graph path.firstStep).subtype
    exact hfirstCore.to_le (hD ▸ inf_le_right)
  let _ : Fact (IsPGroup 2 D) := ⟨hDp⟩
  let _ : IsElementaryAbelian 2 D :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
      ((Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp hfrattini)
  have hDD : ⁅D, D⁆ ≤ center := by
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_).le.trans bot_le
    intro member hmember
    rw [Subgroup.mem_centralizer_iff]
    intro other hother
    exact congrArg Subtype.val (mul_comm (⟨other, hother⟩ : D) (⟨member, hmember⟩ : D))
  have hQComm : ⁅Q, D⁆ ≤ center := by
    rw [data.core_generation]
    exact sup_commutator_le_of_normalizes initial center (oldPart ⊔ newPart) D D
      hcenterNormal (sup_le (inf_le_right.trans hcore) (inf_le_right.trans hcore)) hDN
      (sup_commutator_le_of_normalizes initial center oldPart newPart D hcenterNormal
        (inf_le_right.trans hcore) (inf_le_right.trans hcore) holdComm hnewComm) hDD
  have hsylow : IsSylowTwoIn (L ⊓ S) L := by
    apply eight_six_sylow_intersection_of_residual_le initial L S data.closure_le
      (SevenSix.edge_sylow_data hyp graph path).1
    exact (graph.twoResidualAt_def path.a).symm.le.trans data.residual_le
  have hgen : twoResidualIn L ⊔ (first ⊔ Q) = L := by
    rw [← data.sylow_intersection]
    exact SevenSix.twoResidualIn_sup_sylow hsylow
  apply le_antisymm ?_
    (data.residual_commutator.symm.le.trans
      (Subgroup.commutator_mono le_rfl (SevenSix.twoResidualIn_le L)))
  rw [Subgroup.commutator_comm, ← hgen]
  apply sup_commutator_le_of_normalizes initial center (twoResidualIn L) (first ⊔ Q) D
    hcenterNormal ((SevenSix.twoResidualIn_le L).trans data.closure_le)
    ((sup_le hfirstL hQL).trans data.closure_le)
  · rw [Subgroup.commutator_comm]
    exact data.residual_commutator.le
  · exact sup_commutator_le_of_normalizes initial center first Q D hcenterNormal
      (hfirstL.trans data.closure_le) (hQL.trans data.closure_le) hfirstComm hQComm

end Stellmacher.SectionEight
