module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSylowTransport
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.UpperCentralSeriesPullback
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicCentralizers.Plane
public import Theory.SpecificGroups.ReeTwo.CoreParabolicStructure
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.NaturalOrderFour

/-!
# The intrinsic second core of the actual middle subgroup

The actual middle has center Z. Faithfulness of the natural H/Q action
puts its second center in Q, hence in the first core, whose second center
is U. The native order-four quotient actor has only two fixed points on
U/Z, bounding the second center by four. The original invariant plane has
order four and central quotient modulo Z, so it is exactly that center.
The source centralizer and second-parabolic intersection now identify
C_T_F(Z₂(T_F)) with the unchanged A.

All actors, kernels, and subgroups are the original TypeRu source objects.
Source: Aschbacher–Smith J.4.4–5, printed pp.441–442.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

private theorem natural_fixed_iff (h:d.toTypeRuSetup.H) (u:d.toTypeRuSetup.U) :
    d.ru2.naturalAction.action (d.ru2.quotientMap h) (d.ru2.natural.coordinates u).toAdd=
      (d.ru2.natural.coordinates u).toAdd ↔ ⁅(h:G),(u:G)⁆∈d.toTypeRuSetup.Z := by
  have he:=d.ru2.natural.equivariant h u
  simp only [MonoidHom.comp_apply] at he
  rw [←he]
  rw [Multiplicative.toAdd.injective.eq_iff,←mul_inv_eq_one,←map_inv,←map_mul,
    d.ru2.natural.coordinates_eq_one_iff]
  rfl

private theorem natural_trivial_of_commutators (h:d.toTypeRuSetup.H)
    (hc:∀u:d.toTypeRuSetup.U,⁅(h:G),(u:G)⁆∈d.toTypeRuSetup.Z) :
    (h:G)∈d.toTypeRuSetup.Q := by
  apply (d.toTypeRuSetup.natural_action_eq_one_iff h).mp
  apply LinearMap.ext
  intro v
  change d.ru2.naturalAction.action (d.ru2.quotientMap h) v=v
  obtain ⟨u,hu⟩:=d.ru2.natural.onto (Multiplicative.ofAdd v)
  have hh:=(natural_fixed_iff h u).mpr (hc u)
  simpa only [hu,toAdd_ofAdd] using hh

theorem Plane.firstCore_le_T_F (B5:Sylow 5 d.toTypeRuSetup.H) :
    fiveHyperplane d B5≤p.T_F B5 :=
  sup_le_sup (p.Q₀_le_S₂.trans (p.S₂_le_A B5)) le_rfl

theorem SourceChoice.T_F_inf_Q (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    p.T_F B5⊓d.toTypeRuSetup.Q=fiveHyperplane d B5 := by
  apply le_antisymm
  · exact (inf_le_inf_right _ (p.T_F_le_F₁ B5)).trans_eq (s.F₁_inf_Q p B5 hi)
  · exact le_inf (p.firstCore_le_T_F B5) (fiveHyperplane_le_Q d B5)

theorem Plane.T_F_center (B5:Sylow 5 d.toTypeRuSetup.H) :
    (center (p.T_F B5)).map (p.T_F B5).subtype=d.toTypeRuSetup.Z := by
  have hC:=centralizer_of_Q₅_le d B5 (show Q₅ d B5≤p.T_F B5 from le_sup_right)
    ((p.T_F_le_F₁ B5).trans (p.F₁_le_H B5))
  have hZM:d.toTypeRuSetup.Z≤p.T_F B5:=d.ru2.natural.kernel_le.trans
    ((U_le_fiveHyperplane d B5).trans (p.firstCore_le_T_F B5))
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    apply hC.le
    intro y hy
    exact congrArg (fun a:p.T_F B5=>(a:G)) (mem_center_iff.mp hx ⟨y,hy⟩)
  · intro z hz
    refine ⟨⟨z,hZM hz⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    apply Subtype.ext
    exact hC.ge hz y y.property

theorem SourceChoice.firstCore_secondCenter (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    (Subgroup.upperCentralSeries (fiveHyperplane d B5) 2).map (fiveHyperplane d B5).subtype=
      d.toTypeRuSetup.U := by
  obtain ⟨e,_,_,_,_,_,_⟩:=s.exists_firstCore_five_marking B5 hi
  have hd:(_root_.commutator (fiveHyperplane d B5)).map e.toMonoidHom=
      _root_.commutator ReeTwo.Core:=by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have he:Subgroup.upperCentralSeries (fiveHyperplane d B5) 2=
      _root_.commutator (fiveHyperplane d B5):=by
    rw [←Subgroup.comap_upperCentralSeries e 2,ReeTwo.Core.second_center_eq_derived,←hd]
    change ((_root_.commutator (fiveHyperplane d B5)).map e.toMonoidHom).comap e.toMonoidHom=_
    exact comap_map_eq_self_of_injective e.injective _
  rw [he,map_subtype_commutator,firstCore_derived]

/-- The second center of the unchanged middle subgroup lies in the actual U. -/
theorem SourceChoice.T_F_secondCenter_le_U (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    (Subgroup.upperCentralSeries (p.T_F B5) 2).map (p.T_F B5).subtype≤d.toTypeRuSetup.U := by
  let M:=p.T_F B5
  let R:=fiveHyperplane d B5
  have hRM:R≤M:=p.firstCore_le_T_F B5
  have hMH:M≤d.toTypeRuSetup.H:=(p.T_F_le_F₁ B5).trans (p.F₁_le_H B5)
  have hUM:d.toTypeRuSetup.U≤M:=(U_le_fiveHyperplane d B5).trans hRM
  rintro _ ⟨x,hx,rfl⟩
  have hcomm:∀y:M,⁅(x:G),(y:G)⁆∈d.toTypeRuSetup.Z:=by
    intro y
    have hh:=(Subgroup.mem_upperCentralSeries_succ_iff (n:=1) (G:=M)).mp hx y
    rw [Subgroup.upperCentralSeries_one] at hh
    have hm:=mem_map_of_mem M.subtype hh
    rw [p.T_F_center B5] at hm
    exact hm
  have hxQ:(x:G)∈d.toTypeRuSetup.Q:=natural_trivial_of_commutators (d:=d)
    ⟨x,hMH x.property⟩ (fun u=>hcomm ⟨u,hUM u.property⟩)
  have hxR:(x:G)∈R:=(s.T_F_inf_Q B5 hi).le ⟨x.property,hxQ⟩
  let xR:R:=⟨x,hxR⟩
  have hsec:xR∈Subgroup.upperCentralSeries R 2:=by
    apply Subgroup.comap_upperCentralSeries_le_of_injective (inclusion hRM) (inclusion_injective hRM) 2
    change inclusion hRM xR∈Subgroup.upperCentralSeries M 2
    have he:inclusion hRM xR=x:=Subtype.ext rfl
    rw [he]
    exact hx
  have hm:=mem_map_of_mem R.subtype hsec
  rw [s.firstCore_secondCenter B5 hi] at hm
  exact hm

/-- The original invariant plane lies in the second center of the middle. -/
theorem Plane.plane_le_T_F_secondCenter (B5:Sylow 5 d.toTypeRuSetup.H) :
    p.group≤(Subgroup.upperCentralSeries (p.T_F B5) 2).map (p.T_F B5).subtype := by
  let M:=p.T_F B5
  have hVM:p.group≤M:=p.le_seed.trans (p.V_le_S₂.trans ((p.S₂_le_A B5).trans le_sup_left))
  have hZM:d.toTypeRuSetup.Z≤M:=p.point_le.trans hVM
  have hMT:M≤(d.T:Subgroup G):=(sup_le_sup_right (p.A_le_R₂ B5) _).trans_eq (p.R₂_sup_Q₅ B5)
  have hzi:d.toTypeRuSetup.Z.relIndex p.group=2:=by
    have hc:=(d.toTypeRuSetup.Z.subgroupOf p.group).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe p.point_le).toEquiv,d.card_Z,p.card] at hc
    change d.toTypeRuSetup.Z.relIndex p.group*2=4 at hc
    omega
  have hcom:⁅p.group,M⁆≤d.toTypeRuSetup.Z:=commutator_le_of_normalized_index_two
    _ _ _ p.point_le hzi (hMT.trans p.normalized)
    ((hMT.trans d.toTypeRuSetup.T_le_H).trans (Subgroup.centralizer_le_normalizer _))
  have hcM:center M=d.toTypeRuSetup.Z.subgroupOf M:=by
    apply map_injective M.subtype_injective
    rw [p.T_F_center,map_subgroupOf_eq_of_le hZM]
  intro x hx
  refine ⟨⟨x,hVM hx⟩,Subgroup.mem_upperCentralSeries_succ_iff.mpr ?_,rfl⟩
  intro y
  rw [Subgroup.upperCentralSeries_one,hcM]
  exact hcom (commutator_mem_commutator hx y.property)

/-- The faithful order-four natural action bounds the second center by four. -/
theorem SourceChoice.T_F_secondCenter_card_le_four (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (g:p.T_F B5) (hg:orderOf (d.ru2.quotientMap
      (inclusion ((p.T_F_le_F₁ B5).trans (p.F₁_le_H B5)) g))=4) :
    Nat.card (Subgroup.upperCentralSeries (p.T_F B5) 2)≤4 := by
  let M:=p.T_F B5
  let E:Subgroup G:=(Subgroup.upperCentralSeries M 2).map M.subtype
  have hEU:E≤d.toTypeRuSetup.U:=s.T_F_secondCenter_le_U B5 hi
  let f:E→*Multiplicative FourSpace:=d.ru2.natural.coordinates.comp (inclusion hEU)
  let gH:d.toTypeRuSetup.H:=inclusion ((p.T_F_le_F₁ B5).trans (p.F₁_le_H B5)) g
  let V:Type:= {v:FourSpace //d.ru2.naturalAction.action (d.ru2.quotientMap gH) v=v}
  have hfix:∀x:E,d.ru2.naturalAction.action (d.ru2.quotientMap gH) (f x).toAdd=(f x).toAdd:=by
    intro x
    apply (natural_fixed_iff gH (inclusion hEU x)).mpr
    obtain ⟨y,hy,he⟩:=x.property
    have hh:=Subgroup.mem_upperCentralSeries_succ_iff.mp hy g
    rw [Subgroup.upperCentralSeries_one] at hh
    have hm:=mem_map_of_mem M.subtype hh
    rw [p.T_F_center B5] at hm
    have hm':⁅(x:G),(g:G)⁆∈d.toTypeRuSetup.Z:=by
      rw [←he]
      exact hm
    rw [←commutatorElement_inv]
    exact inv_mem hm'
  have hrc:Nat.card f.range≤2:=by
    let j:f.range→V:=fun x=>⟨x.val.toAdd,by
      obtain ⟨y,he⟩:=x.property
      rw [←he]
      exact hfix y⟩
    have hj:Function.Injective j:=by
      intro x y he
      apply Subtype.ext
      exact Multiplicative.toAdd.injective (congrArg (fun a:V=>a.val) he)
    have hc:=Nat.card_le_card_of_injective j hj
    rw [d.toTypeRuSetup.natural_order_four_fixed_card gH hg] at hc
    exact hc
  have hkc:Nat.card f.ker≤2:=by
    let j:f.ker→d.toTypeRuSetup.Z:=fun x=>⟨x.val.val,by
      exact (d.ru2.natural.coordinates_eq_one_iff (inclusion hEU x.val)).mp x.property⟩
    have hj:Function.Injective j:=by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a:d.toTypeRuSetup.Z=>(a:G)) he
    exact (Nat.card_le_card_of_injective j hj).trans_eq d.card_Z
  have hc:=f.ker.card_mul_index
  rw [index_ker] at hc
  have hE:Nat.card E≤4:=by nlinarith
  rwa [card_map_of_injective M.subtype_injective] at hE

/-- The second center of the actual middle is precisely the original plane. -/
theorem SourceChoice.T_F_secondCenter (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    (Subgroup.upperCentralSeries (p.T_F B5) 2).map (p.T_F B5).subtype=p.group := by
  obtain ⟨g,hg⟩:=s.exists_T_F_order_four_mod_Q B5 hi
  apply (eq_of_le_of_card_ge (p.plane_le_T_F_secondCenter B5) ?_).symm
  rw [p.card,card_map_of_injective (p.T_F B5).subtype_injective]
  exact s.T_F_secondCenter_card_le_four B5 hi g hg

omit [Finite G] in
private theorem map_centralizer_subtype (M:Subgroup G) (N:Subgroup M) :
    (centralizer (N:Set M)).map M.subtype=M⊓centralizer (N.map M.subtype:Set G) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rintro _ ⟨y,hy,rfl⟩
    exact congrArg (fun a:M=>(a:G)) (hx y hy)
  · rintro x ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    intro y hy
    apply Subtype.ext
    exact hc y (mem_map_of_mem M.subtype hy)

/-- The source A is the intrinsic centralizer of the middle's second center. -/
theorem SourceChoice.T_F_intrinsic_A (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    (centralizer (Subgroup.upperCentralSeries (p.T_F B5) 2:Set (p.T_F B5))).map
      (p.T_F B5).subtype=p.A B5 := by
  rw [map_centralizer_subtype,s.T_F_secondCenter B5 hi]
  obtain ⟨X,_hx,hmodel,_hgen,_hcore,_hf⟩:=s.exists_secondParabolic p B5 hi
  have hcap:p.T_F B5⊓p.R₂=p.A B5:=by
    apply le_antisymm
    · exact (inf_le_inf_right _ (p.T_F_le_F₂ B5 X)).trans_eq (p.F₂_inf_R₂ B5 X hmodel)
    · exact le_inf le_sup_left (p.A_le_R₂ B5)
  calc
    p.T_F B5⊓centralizer (p.group:Set G)=
        (p.T_F B5⊓p.parabolic)⊓centralizer (p.group:Set G) := by
          rw [inf_eq_left.mpr (p.T_F_le_parabolic B5)]
    _=p.T_F B5⊓p.R₂ := by rw [inf_assoc,p.parabolic_inf_centralizer]
    _=p.A B5:=hcap

end CFSG.Quasithin.ChapterJ.RuSubgroup
