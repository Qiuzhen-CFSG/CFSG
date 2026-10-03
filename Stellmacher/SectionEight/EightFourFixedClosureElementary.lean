module
public import Stellmacher.TwoResidualSylowSupplement
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Theory.GroupTheory.CenterFreeOddImageCore
public import Stellmacher.SectionEight.EightFourFixedClosureControl
public import Stellmacher.QuotientModuleCommutator
public import Stellmacher.OmegaOneCenterMap
public import Stellmacher.SectionOne.OneSevenFixedCommutator
public import Stellmacher.SectionEight.LemmaEightOneResidualJoin

/-!
# The elementary fixed-center closure in Stellmacher (8.4)

For a noncommuting critical pair in the actual local context with central
first-step vertex center,
the normal closure of the initial barred J-fixed subgroup in that first-step
stabilizer is elementary abelian of exponent two. The exact quotient witness,
initial closure, and nontrivial-closure branch are retained. The original
canonical signature remains an exact wrapper through the same local graph.

The centrality alternative in (7.3) makes the initial stabilizer center-free.
Its two-residual supplements a Sylow subgroup, so the normal-two-subgroup
centralizer theorem gives C_{Q_a}(E_a)=1. The full core assertion supports
the commutator calculation in source (8); its restriction to Z_a is preserved
for the order-four reduction in (8.5). These two calculations use the actual
local context; their canonical names are exact local-context wrappers. The
natural SL2(2) factor calculation
from (1.7) covers the J-fixed vectors by E-fixed vectors and J-commutators.
The first summand is therefore zero. The opposite-center closure S1 maps
onto J, so witness compatibility puts the fixed subgroup F in [Z_a,S1],
which lies in S1 by normality. Source (3) also says F centralizes S1.
Thus F lies in the omega-one center of S1, a characteristic subgroup of the
normal container. Its entire first-step normal closure remains there and
is elementary abelian.

This supplies the elementary actor needed for source (6)(ii), using precisely
the initial closure from source (4), not a transported terminal closure.
Source: Stellmacher, Journal of Algebra 190 (1997), (8.4), source (2)--(4),
printed pp.38--39, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
/-- The initial two-core has trivial centralizer of its stabilizer residual. -/
public theorem eight_four_initial_core_residual_centralizer_trivial_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    QAt ctx.Γ ctx.criticalPath.a ⊓
      Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a : Set H) = ⊥ := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Pb := stabilizer Γ cp.firstStep
  let Q := pCore 2 P
  let E := twoResidualAmbient (⊤ : Subgroup P)
  have ha : cp.a ∈ neighborhood Γ cp.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  have h73 := lemma_seven_three h Γ
  have hPcenter : Subgroup.center P = ⊥ := by
    let T : Sylow 2 (↥(Pb ⊓ P)) := default
    have hdata := edge_sectionThree_data h Γ ha T
    have halt := h73.centralizer_alternative cp.firstStep cp.a ha T
    have hZeq : z Γ cp.firstStep = omegaOneCenter Pb := by
      rcases halt with heq | heq
      · have hWPb : sylowTwoAmbient (Pb ⊓ P) T ≤ Pb :=
          (Subgroup.map_subtype_le _).trans inf_le_left
        have hWC : sylowTwoAmbient (Pb ⊓ P) T ≤ Subgroup.centralizer (z Γ cp.firstStep : Set H) :=
          hWPb.trans (Subgroup.le_centralizer_iff.mp
            (hcenter.trans (SevenSix.centerAmbient_le_centralizer Pb)))
        rw [inf_eq_left.mpr hWC] at heq
        have hcore : q Γ cp.firstStep = twoCoreAmbient Pb := Γ.twoCoreAt_def cp.firstStep
        exact (hdata.2.1.1.2.2.2 (heq.trans hcore)).elim
      · exact heq.1
    exact h73.center_neighbor_trivial cp.firstStep cp.a ha hZeq
  have hQmap : Q.map P.subtype = q Γ cp.a :=
    (Γ.twoCoreAt_def cp.a).symm
  have hQP : q Γ cp.a ≤ P := hQmap ▸ Subgroup.map_subtype_le _
  have hEmap : E.map P.subtype = e Γ cp.a := by
    have hm := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) P.subtype P
      (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
    exact hm.trans (Γ.twoResidualAt_def cp.a).symm
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  obtain ⟨_, T, _⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hzero := Subgroup.inf_centralizer_eq_bot_of_centerfree_sylow_supplement
    T E Q (twoResidualAmbient_top_sup_sylow T)
    (pCore_isPGroup (p := 2) (G := P)) hPcenter
  apply le_bot_iff.mp
  intro x hx
  let xP : P := ⟨x, hQP hx.1⟩
  have hxQ : xP ∈ Q := by
    obtain ⟨r, hr, hrx⟩ := hQmap ▸ (show x ∈ q Γ cp.a from hx.1)
    have heq : r = xP := Subtype.ext hrx
    exact heq ▸ hr
  have hxE : xP ∈ Subgroup.centralizer (E : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    apply P.subtype_injective
    have hrE : (r : H) ∈ e Γ cp.a := hEmap ▸ Subgroup.mem_map_of_mem P.subtype hr
    exact Subgroup.mem_centralizer_iff.mp hx.2 r hrE
  have hxbot : xP ∈ (⊥ : Subgroup P) := hzero ▸ (show xP ∈ Q ⊓ Subgroup.centralizer (E : Set P) from ⟨hxQ,hxE⟩)
  have hxone : xP = 1 := hxbot
  exact congrArg Subtype.val hxone

/-- The initial center has trivial centralizer of its stabilizer residual. -/
public theorem eight_four_initial_residual_center_trivial_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ZAt ctx.Γ ctx.criticalPath.a ⊓
      Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a : Set H) = ⊥ := by
  have hq : ZAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.a :=
    ((lemma_seven_three (ctx.sectionSeven) ctx.Γ).center_core
      ctx.criticalPath.a ctx.criticalPath.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj)).trans
      (Subgroup.map_subtype_le _)
  exact le_bot_iff.mp ((inf_le_inf_right _ hq).trans_eq
    (eight_four_initial_core_residual_centralizer_trivial_local ctx hcenter))



public theorem eight_four_initial_core_residual_centralizer_trivial
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    QAt ctx.Γ ctx.criticalPath.a ⊓
      Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a : Set H) = ⊥ := by
  exact eight_four_initial_core_residual_centralizer_trivial_local ctx.toLocalContext hcenter

public theorem eight_four_initial_residual_center_trivial
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ZAt ctx.Γ ctx.criticalPath.a ⊓
      Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a : Set H) = ⊥ := by
  exact eight_four_initial_residual_center_trivial_local ctx.toLocalContext hcenter

private theorem closure_elementary_of_central_normal_container
    {H : Type u} [Group H] (F P K : Subgroup H)
    (hF : IsElementaryAbelian 2 F) (hFK : F ≤ K)
    (hFc : F ≤ Subgroup.centralizer (K : Set H))
    (hPK : P ≤ Subgroup.normalizer (K : Set H)) :
    IsElementaryAbelian 2
      ((Subgroup.normalClosure (F.subgroupOf P : Set P)).map P.subtype) := by
  let KN := K.subgroupOf P
  let ZN := Subgroup.center KN
  let W := omega₁ (G := ZN) (p := 2)
  let A := (W.map ZN.subtype).map KN.subtype
  let _ : KN.Normal := by
    constructor
    intro x hx p
    exact (Subgroup.mem_normalizer_iff.mp (hPK p.property) x).mp hx
  let _ : ZN.Characteristic := Subgroup.centerCharacteristic
  let _ : W.Characteristic := omega₁_characteristic ZN
  let _ : (W.map ZN.subtype).Characteristic := inferInstance
  let _ : A.Normal := ConjAct.normal_of_characteristic_of_normal
  let _ := hF
  have hFA : F.subgroupOf P ≤ A := by
    intro f hf
    change f ∈ omegaOneCenterAmbient KN
    apply (mem_omegaOneCenterAmbient_iff KN f).mpr
    refine ⟨hFK hf, ?_, ?_⟩
    · apply P.subtype_injective
      exact elemPow_eq_one_of_isElementaryAbelian (f : H) hf
    · intro k hk
      apply P.subtype_injective
      exact Subgroup.mem_centralizer_iff.mp (hFc hf) k hk
  have hCA : Subgroup.normalClosure (F.subgroupOf P : Set P) ≤ A :=
    Subgroup.normalClosure_le_normal hFA
  let _ : IsElementaryAbelian 2 A := omegaOneCenterAmbient_elementaryAbelian KN
  let C := Subgroup.normalClosure (F.subgroupOf P : Set P)
  have hC : IsElementaryAbelian 2 C :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
        (congrArg (fun z : A => (z : P)) ((IsMulCommutative.is_comm (M := A)).comm
          ⟨x,hCA x.property⟩ ⟨y,hCA y.property⟩))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : P) (hCA x.property)) }
  let _ := hC
  exact IsElementaryAbelian.map P.subtype

/-- The initial normal closure of the barred fixed center is elementary abelian. -/
public theorem eight_four_fixed_closure_elementary_local
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
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    IsElementaryAbelian 2 ((Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype) := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Pb := GAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  let K := oppositeClosureLocal ctx
  let F := w.oneJFixedPoints S
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  let Sb := (S.subgroupOf P).map w.projection
  let J := SectionOne.oneJ (V := Za) Sb
  let E := SectionOne.oneE (V := Za) Sb
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have h73 := lemma_seven_three h Γ
  have hZaS : Za ≤ S := (h73.center_core cp.a cp.firstStep hfirst).trans
    ((Subgroup.map_subtype_le _).trans (SevenSix.local_cores_le_edge_sylow h Γ cp).1)
  have hZaPb : Za ≤ Pb := hZaS.trans (cp.S_le_edge_stabilizers.trans inf_le_right)
  have hSP : S ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hKP : K ≤ P := (opposite_closure_normal_sylow_local ctx).1.trans hSP
  have hKb : NormalIn K Pb := opposite_closure_normal_next_local ctx
  have hPK : Pb ≤ Subgroup.normalizer (K : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKb.1).mp hKb.2
  have himage : (K.subgroupOf P).map w.projection = J :=
    eight_four_opposite_closure_image_local ctx hcenter w hbranch
  have hfixed : F = Za ⊓ Subgroup.centralizer (K : Set H) :=
    fixed_center_eq_opposite_closure_centralizer_of_image_local ctx w himage
  have hlen := cp.length_pos
  let last : Γ.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have he := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hi, cp.path_end] at he
    exact Γ.adjacent_symm he
  have hlast := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hlast
  have hZendP : z Γ cp.a' ≤ P := (lemma_seven_four h Γ cp).reverse_containment.1
  have hnotcentral : ¬ z Γ cp.a' ≤ Subgroup.centralizer (z Γ cp.a : Set H) := by
    intro hc
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
  have hlocal := local_quotient_hypotheses h Γ cp.a hfirst w (z Γ cp.a')
    hZendP hnotcentral
  obtain ⟨_, U, hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUS]
  have hcover := SectionOne.oneSeven_fixed_le_fixed_sup_commutator hlocal Ub
  rw [hUb] at hcover
  have hEzero : FixedPoints.subgroup E Za = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hres : ((EAt Γ cp.a).subgroupOf P).map w.projection ≤ E := by
      rw [show E = _ from lemma_eight_one_residual_join_local ctx w]
      exact le_sup_left
    have hvres : v ∈ FixedPoints.subgroup
        (((EAt Γ cp.a).subgroupOf P).map w.projection) Za :=
      fun r => hv ⟨r, hres r.property⟩
    have hEaP : EAt Γ cp.a ≤ P := by
      rw [show EAt Γ cp.a = twoResidualIn P from Γ.twoResidualAt_def cp.a]
      exact Subgroup.map_subtype_le _
    have hvmap := Subgroup.mem_map_of_mem Za.subtype hvres
    rw [w.fixedPoints_map_subtype (EAt Γ cp.a) hEaP,
      eight_four_initial_residual_center_trivial_local ctx hcenter] at hvmap
    exact Subtype.ext hvmap
  have hFcomm : F ≤ ⁅Za, K⁆ := by
    have hm := Subgroup.map_mono hcover (f := Za.subtype)
    change F ≤ (FixedPoints.subgroup E Za ⊔ commutatorAction J Za).map Za.subtype at hm
    rw [hEzero, bot_sup_eq, ← himage,
      w.commutatorAction_image_map_subtype K hKP] at hm
    exact hm
  have hFK : F ≤ K := hFcomm.trans
    (Subgroup.le_normalizer_iff_commutator_le_right.mp (hZaPb.trans hPK))
  have hFelem : IsElementaryAbelian 2 F := by
    let _ : IsElementaryAbelian 2 (FixedPoints.subgroup J Za) :=
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun v =>
          Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 Za) v) }
    exact IsElementaryAbelian.map Za.subtype
  exact closure_elementary_of_central_normal_container F Pb K hFelem hFK
    (hfixed ▸ inf_le_right) hPK


public theorem eight_four_fixed_closure_elementary
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
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    IsElementaryAbelian 2 ((Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype) := by
  exact eight_four_fixed_closure_elementary_local ctx.toLocalContext hcenter w hbranch

end Stellmacher.SectionEight
