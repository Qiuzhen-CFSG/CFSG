module
public import Stellmacher.SectionEight.LemmaEightOne
public import Stellmacher.QuotientModuleOffenderFixedPoints
public import Stellmacher.SectionOne.OneSevenFixedSpaceFixer
public import Stellmacher.SectionOne.OneSevenSubgroupSupportLine
public import Stellmacher.SectionOne.OneSevenCommutatorFixed
public import Stellmacher.SectionEight.EightFourLengthTwoStarCommutation

/-!
# The chosen length-two star acts on the whole initial center modulo the terminal center

In the actual local central-first-step branch of (8.4), retain the supplied
faithful witness and the actual covariant normal stars. Suppose a terminal
stabilizer element chooses a neighbor whose module, together with the first
module, contains the terminal residual, and its star lies in the first core.
Then that star's commutator with the whole initial center lies in the terminal
center. The core containment places the star in the original edge Sylow;
no containment of the terminal core in that Sylow is assumed.

The two stars commute, and their own-module centrality makes the chosen star
intersect the original fixed subgroup trivially: the intersection centralizes
both modules, hence the residual, inside its core. The pointwise-fixer identity
puts the chosen star's faithful image in the canonical J. Decompose the initial
center into its genuine one-seven supports and the fixed complement. On a
support moved by the terminal center, the support-line theorem supplies the
required bound. An unmoved support lies in the terminal core by (7.4), so it
normalizes the chosen star. Its commutator lies in both the star and the
J-fixed subgroup by J's quadratic action, and is therefore trivial. J fixes
the remaining complement. Multiplicativity of action differences joins these
bounds across the original module decomposition.

This expands the factor argument in Stellmacher (8.4)(8), Journal of Algebra
190 (1997), p39, refs/files/stellmacher-n-group.pdf. It strengthens the selected
support bound to the whole initial center using the actual length-two geometry;
it does not identify a selected four-element support with that whole center.
The private reduction and public theorem retain the same supplied quotient
action in the local context. The original canonical theorem is an exact
wrapper, including its selected-star core-containment hypothesis.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
open scoped commutatorElement IsMulCommutative

private theorem full_center_bound
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (T : Subgroup H) (hTS : T ≤ S)
    (hTF : ⁅T,w.oneJFixedPoints S⁆ = ⊥)
    (hQT : QAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer T)
    (hdisj : T ⊓ w.oneJFixedPoints S = ⊥) :
    ⁅T,ZAt ctx.Γ ctx.criticalPath.a⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a' := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let P := GAt Γ cp.a
  let V := ZAt Γ cp.a
  let Y := ZAt Γ cp.a'
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom V w.action
  let Sb := (S.subgroupOf P).map w.projection
  let J := SectionOne.oneJ (V := V) Sb
  let K := (Y.subgroupOf P).map w.projection
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have h74 := lemma_seven_four h Γ cp
  have hYP : Y ≤ P := h74.reverse_containment.1
  have hSP : S ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hpos := cp.length_pos
  let last := cp.path ⟨cp.length-1,by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have he := cp.path_adj ⟨cp.length-1,by omega⟩
    have hi : (⟨cp.length-1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    exact Γ.adjacent_symm he
  have hlast := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hlast
  have hnotcentral : ¬ Y ≤ Subgroup.centralizer (V : Set H) := by
    intro hc
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
  have hlocal := local_quotient_hypotheses h Γ cp.a hfirst w Y hYP hnotcentral
  obtain ⟨_, U, hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUS]
  have hKJ : K ≤ J := le_sSup (eight_five_offender_local ctx w).1
  let E := SectionOne.oneSevenGenerated (G := w.X) (V := V)
  let Factors := SectionOne.oneSevenFactors (G := w.X) (V := V)
  obtain ⟨hEnormal,hprod,_⟩ := SectionOne.oneSeven_global_product hlocal Ub
  change IsInternalDirectProduct E Factors at hprod
  let _ : E.Normal := hEnormal
  have hJid : J = (Ub : Subgroup w.X) ⊓ E := by
    simpa only [hUb] using (SectionOne.oneSeven_global_identification hlocal Ub).1
  let I := {D : Subgroup w.X // D ∈ Factors}
  let n := Fintype.card I
  let eI : Fin n ≃ I := (Fintype.equivFin I).symm
  let Df : Fin n → Subgroup w.X := fun i => (eI i).val
  have hDi (i : Fin n) : Df i ∈ Factors := (eI i).property
  have hinj : Function.Injective Df := by intro i j he; exact eI.injective (Subtype.ext he)
  have hDf (i) : SectionOne.IsOneSevenFactor (V := V) (Df i) :=
    (SectionOne.mem_oneSevenFactors_iff _).mp (hDi i)
  have hgen : E = ⨆ i : Fin n, Df i := by
    rw [hprod.1]
    apply le_antisymm
    · apply iSup_le
      intro D
      obtain ⟨i,rfl⟩ := eI.surjective D
      exact le_iSup Df i
    · apply iSup_le
      intro i
      exact le_iSup (fun D : I => (D : Subgroup w.X)) (eI i)
  have hfamily : IsInternalDirectProductFamily E Df := by
    refine ⟨hgen,?_,?_⟩
    · intro i j hij
      exact hprod.2.2.1 (Df i) (hDi i) (Df j) (hDi j) (fun he => hij (hinj he))
    · intro i j hij
      exact hprod.2.2.2 (Df i) (hDi i) (Df j) (hDi j) (fun he => hij (hinj he))
  have hDN (i) : ((Df i).subgroupOf E).Normal := hprod.2.1 (Df i) (hDi i)
  let Vf := fun i => commutatorAction (Df i) V
  have hVprod := SectionOne.oneSevenFactor_module_product hlocal Df hDf hinj E hgen
  have hVgen : FixedPoints.subgroup E V ⊔ (⨆ i, Vf i) = ⊤ := by
    simpa only [iSup_option] using hVprod.1.symm
  have hKE : K ≤ E := hKJ.trans (hJid ▸ inf_le_right)
  have hTP : T ≤ P := hTS.trans hSP
  have hTbarJ : (T.subgroupOf P).map w.projection ≤ J := by
    have hfixer := SectionOne.oneSeven_fixedSpace_fixer_eq_oneJ_unconditional hlocal Ub
    rw [hUb] at hfixer
    change _ ≤ SectionOne.oneJ (V := V) Sb
    rw [← hfixer]
    rintro t ⟨y,hy,rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro v hv
    apply Subtype.ext
    change ((w.action (w.projection y)) v : H) = (v : H)
    rw [w.action_compatible]
    have hvF : (v : H) ∈ w.oneJFixedPoints S := Subgroup.mem_map_of_mem V.subtype hv
    have hyC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hTF hy
    have heq : (v : H) * (y : H) = (y : H) * (v : H) :=
      Subgroup.mem_centralizer_iff.mp hyC v hvF
    rw [← heq,mul_assoc,mul_inv_cancel,mul_one]
  have hRY : ⁅V,Y⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((h74.first_containment.1.trans h74.first_containment.2).trans (stabilizer_le_normalizer_z Γ cp.a'))
  have hquad : commutatorAction J V ≤ FixedPoints.subgroup J V := by
    have hh := SectionOne.oneSeven_commutator_le_fixed hlocal Ub
    rw [hUb] at hh
    exact hh
  have hdelta (t : H) (ht : t ∈ T) (v : V) :
      ((v⁻¹ * ((w.projection ⟨t,hTP ht⟩) • v) : V) : H) = ⁅t,(v : H)⁆ := by
    change (v : H)⁻¹ * ((w.action (w.projection ⟨t,hTP ht⟩)) v : H) = ⁅t,(v : H)⁆
    rw [w.action_compatible]
    have hcomm := congrArg (fun z : V => (z : H))
      ((IsMulCommutative.is_comm (M := V)).comm v⁻¹
        ((w.action (w.projection ⟨t,hTP ht⟩)) v))
    change (v : H)⁻¹ * (t * (v : H) * t⁻¹) = (t * (v : H) * t⁻¹) * (v : H)⁻¹
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,w.action_compatible] using hcomm
  have hdiffF (t : H) (ht : t ∈ T) (v : V) : ⁅t,(v : H)⁆ ∈ w.oneJFixedPoints S := by
    have htJ : w.projection ⟨t,hTP ht⟩ ∈ J :=
      hTbarJ (Subgroup.mem_map_of_mem w.projection ht)
    have hd : v⁻¹ * ((w.projection ⟨t,hTP ht⟩) • v) ∈ commutatorAction J V := by
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨_,htJ⟩,v,rfl⟩
    exact hdelta t ht v ▸ Subgroup.mem_map_of_mem V.subtype (hquad hd)
  have hfactor (i : Fin n) : ⁅T,(Vf i).map V.subtype⁆ ≤ Y := by
    by_cases hi : ∃ k ∈ K, ∃ v ∈ Vf i, k • v ≠ v
    · have hcontrol := SectionOne.oneSevenFactor_subgroup_support_line_control hlocal Ub E Df
        hfamily hinj hDf hDN i K (hKJ.trans hJid.le) hi
      apply Subgroup.commutator_le.mpr
      intro t ht a ha
      obtain ⟨v,hv,rfl⟩ := ha
      have htJ : w.projection ⟨t,hTP ht⟩ ∈ (Ub : Subgroup w.X) ⊓ E :=
        hJid ▸ hTbarJ (Subgroup.mem_map_of_mem w.projection ht)
      have hm := Subgroup.mem_map_of_mem V.subtype (hcontrol _ htJ v hv)
      rw [w.commutatorAction_image_map_subtype Y hYP] at hm
      exact hRY (hdelta t ht v ▸ hm)
    · have hfixed : ∀ k ∈ K, ∀ v ∈ Vf i, k • v = v := by simpa using hi
      let A := (Vf i).map V.subtype
      have hAcentral : A ≤ Subgroup.centralizer (Y : Set H) := by
        rintro a ⟨v,hv,rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have he := congrArg (fun z : V => (z : H))
          (hfixed (w.projection ⟨y,hYP hy⟩) (Subgroup.mem_map_of_mem w.projection hy) v hv)
        change ((w.action (w.projection ⟨y,hYP hy⟩)) v : H) = (v : H) at he
        rw [w.action_compatible] at he
        exact mul_inv_eq_iff_eq_mul.mp he
      have hAP : A ≤ GAt Γ cp.a' := (Subgroup.map_subtype_le _).trans
        (h74.first_containment.1.trans h74.first_containment.2)
      have hAp : IsPGroup 2 A :=
        (IsElementaryAbelian.isPGroup 2 V).to_subgroup _ |>.map V.subtype
      obtain ⟨U,hU⟩ := (hAp.comap_subtype (K := GAt Γ cp.a')).exists_le_sylow
      have hAU : A ≤ sylowTwoAmbient (GAt Γ cp.a') U := by
        intro a ha
        exact ⟨⟨a,hAP ha⟩,hU ha,rfl⟩
      have hAQ : A ≤ QAt Γ cp.a' := by
        change A ≤ q Γ cp.a'
        rw [← (h74.commutator_case ctx.commutator_ne).1 U]
        exact le_inf hAU hAcentral
      have hcommT : ⁅T,A⁆ ≤ T :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp (hAQ.trans hQT)
      apply Subgroup.commutator_le.mpr
      intro t ht a ha
      obtain ⟨v,hv,rfl⟩ := ha
      have hz : ⁅t,(v : H)⁆ ∈ T ⊓ w.oneJFixedPoints S :=
        ⟨hcommT (Subgroup.commutator_mem_commutator ht (Subgroup.mem_map_of_mem V.subtype hv)),
          hdiffF t ht v⟩
      rw [hdisj] at hz
      exact hz ▸ Y.one_mem
  apply Subgroup.commutator_le.mpr
  intro t ht a ha
  let tP : P := ⟨t,hTP ht⟩
  let delta : V →* V :=
    { toFun := fun v => v⁻¹ * ((w.projection tP) • v)
      map_one' := by simp
      map_mul' := by
        intro u v
        simp only [mul_inv_rev,smul_mul']
        ac_rfl }
  have hall : (⊤ : Subgroup V) ≤ (Y.subgroupOf V).comap delta := by
    rw [← hVgen]
    apply sup_le
    · intro v hv
      have htE := hJid.le (hTbarJ (Subgroup.mem_map_of_mem (G := P) w.projection (show tP ∈ T.subgroupOf P from ht)))
      have he : (w.projection tP) • v = v := hv ⟨_,htE.2⟩
      change ((v⁻¹ * ((w.projection tP) • v) : V) : H) ∈ Y
      rw [he,inv_mul_cancel]
      exact Y.one_mem
    · apply iSup_le
      intro i v hv
      change ((v⁻¹ * ((w.projection tP) • v) : V) : H) ∈ Y
      rw [hdelta t ht v]
      exact hfactor i (Subgroup.commutator_mem_commutator ht (Subgroup.mem_map_of_mem V.subtype hv))
  have hh := hall (Subgroup.mem_top (⟨a,ha⟩ : V))
  change ((⟨a,ha⟩⁻¹ * ((w.projection tP) • ⟨a,ha⟩) : V) : H) ∈ Y at hh
  exact hdelta t ht ⟨a,ha⟩ ▸ hh

public theorem eight_four_length_two_full_center_commutator_local
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
    (hcore : C (ctx.Γ.act g ctx.criticalPath.firstStep) ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅C (ctx.Γ.act g ctx.criticalPath.firstStep),ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  have hb : cp.length = 2 := hlen
  let m := Γ.act g cp.firstStep
  have hfirstend : Γ.adjacent cp.a' cp.firstStep := by
    have he := cp.path_adj ⟨1,by omega⟩
    have hi : (⟨1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    have hi0 : (⟨1,by omega⟩ : Fin cp.length).castSucc = ⟨1,by omega⟩ := rfl
    rw [hi0,cp.path_first] at he
    exact Γ.adjacent_symm he
  have hfix : Γ.act g cp.a' = cp.a' := by
    have heq : (stabilizer Γ cp.a' : Set H) = {x | Γ.act x cp.a' = cp.a'} := Γ.stabilizer_def _
    exact Set.ext_iff.mp heq g |>.mp hg
  have hm : Γ.adjacent cp.a' m := by
    have hh := adjacent_act Γ g hfirstend
    simpa only [hfix] using hh
  have hCQ : C cp.firstStep ≤ q Γ cp.a' := by
    rw [hbase]
    exact (eight_four_fixed_closure_control_local ctx hcenter w hbranch).1
  have hCmQ : C m ≤ q Γ cp.a' := by
    have hh := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hCQ
    change (C cp.firstStep).conjBy g⁻¹ ≤ (q Γ cp.a').conjBy g⁻¹ at hh
    rw [← hC g cp.firstStep] at hh
    have hq := SevenSix.q_act Γ g cp.a'
    rw [hfix] at hq
    exact hh.trans_eq hq.symm
  have hQfirst : q Γ cp.a' ≤ stabilizer Γ cp.firstStep :=
    ((lemma_seven_three h Γ).sylow_and_core cp.a' cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hfirstend) default).2.2
  have hQm : q Γ cp.a' ≤ stabilizer Γ m :=
    ((lemma_seven_three h Γ).sylow_and_core cp.a' m
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hm) default).2.2
  have hFFirst : w.oneJFixedPoints S ≤ C cp.firstStep := by
    have hf := (eight_four_fixed_closure_control_local ctx hcenter w hbranch).2
    rw [← hbase] at hf
    exact hf.symm.le.trans inf_le_left
  have hself : ⁅C cp.firstStep,VAt Γ cp.firstStep⁆ = ⊥ := by
    have hh := eight_four_length_two_star_centralizes_module_local ctx hcenter w hbranch C hC hbase hCV hlen 1
    simpa only [ctx.Γ.act_one] using hh
  have hselfm : ⁅C m,VAt Γ m⁆ = ⊥ :=
    eight_four_length_two_star_centralizes_module_local ctx hcenter w hbranch C hC hbase hCV hlen g
  have hmeet : C m ⊓ w.oneJFixedPoints S = ⊥ := by
    apply le_bot_iff.mp
    rw [← eight_four_terminal_core_residual_centralizer_trivial_local ctx hcenter]
    apply le_inf (inf_le_left.trans hCmQ)
    apply le_trans _ (Subgroup.centralizer_le hgen)
    apply Subgroup.le_centralizer_iff.mp
    apply sup_le
    · exact Subgroup.le_centralizer_iff.mpr
        ((inf_le_right.trans hFFirst).trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hself))
    · exact Subgroup.le_centralizer_iff.mpr
        (inf_le_left.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hselfm))
  have hmixed := eight_four_length_two_conjugate_stars_commute_local ctx hcenter w hbranch C hC hbase hCV hCn hlen g hg hgen
  have hTF : ⁅C m,w.oneJFixedPoints S⁆ = ⊥ := by
    apply le_bot_iff.mp
    have hh : ⁅C m,w.oneJFixedPoints S⁆ ≤ ⁅C m,C cp.firstStep⁆ :=
      Subgroup.commutator_mono le_rfl hFFirst
    rw [Subgroup.commutator_comm (C m) (C cp.firstStep),hmixed] at hh
    exact hh
  have hTS : C m ≤ S := hcore.trans (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hQT : q Γ cp.a' ≤ Subgroup.normalizer (C m) := hQm.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (hCn m).1).mp (hCn m).2)
  exact full_center_bound ctx w (C m) hTS hTF hQT hmeet


/-- Canonical specialization preserving the whole-center conclusion and selected star. -/
public theorem eight_four_length_two_full_center_commutator
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
    (hcore : C (ctx.Γ.act g ctx.criticalPath.firstStep) ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅C (ctx.Γ.act g ctx.criticalPath.firstStep),ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a' := by
  exact eight_four_length_two_full_center_commutator_local ctx.toLocalContext
    hcenter w hbranch C hC hbase hCV hCn hlen g hg hgen hcore
end Stellmacher.SectionEight
