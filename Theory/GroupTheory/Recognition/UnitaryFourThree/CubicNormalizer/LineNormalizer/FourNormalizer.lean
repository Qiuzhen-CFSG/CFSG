module
public import Theory.GroupTheory.FourFixedCentralizerNormalizer
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.LocalProduct
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.ReflectionFixed
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneCubicNormalizer
/-!
# The normalizer of the original fixed four preserves the canonical kernel.
The actual plane cubic orbit supplies all three common centralizers.
Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem reflected_four_normalizer_control (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (A:Subgroup G) (hA:A≤R.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16) (htA:m.t∈A)
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hlocal:centralizer z⊓normalizer
      ((((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)=
      centralizer z⊓normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
    let V:=CubicNormalizer.oddKernel X
    normalizer (U:Set G)⊓normalizer ((zpowers z⊔zpowers m.t:Subgroup G):Set G)≤normalizer (V:Set G) ∧
      normalizer (A:Set G)⊓normalizer (U:Set G)≤normalizer (V:Set G) := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
  let V:=CubicNormalizer.oddKernel X
  let S:=zpowers z⊔zpowers m.t
  have hfixed:=R.reflected_line_plane_position h P m A hA htA
  have hSplane:A⊓Subgroup.centralizer (U:Set G)=S:=R.reflected_four_eq_plane_fixed h P m A hA htA
  have hStx:R.cubicSylow X⊓Subgroup.centralizer (U:Set G)=S:=R.reflected_four_eq_sylow_fixed h P m ht hs
  have hS4:Nat.card S=4:=(h.reflected_four P m).2
  let : IsElementaryAbelian 2 S:=(h.reflected_four P m).1
  have hSV:S≤normalizer (V:Set G):=(hStx ▸ inf_le_left).trans
    (inf_le_right.trans (CubicNormalizer.normalizer_normalizes_oddKernel X))
  have hSC:S≤Subgroup.centralizer (U:Set G):=hStx ▸ inf_le_right
  have hVE:IsElementaryAbelian 3 V:=(h.reflected_kernel_of_source_binary_normalizers P m).1
  let :=hVE
  have hV81:Nat.card V=81:=(h.reflected_kernel_of_source_binary_normalizers P m).2
  have hXV:X≤V:=by
    rw[←h.toCentralizerHypothesis.cubic_oddKernel_fixed X (h.cubic_sylow_image_card P) (map_subtype_le _)]
    exact inf_le_left
  have hVC:V≤Subgroup.centralizer (U:Set G):=by
    intro v hv u hu
    exact congrArg Subtype.val (mul_comm' (⟨u,hXV hu.1⟩:V) (⟨v,hv⟩:V))
  have hz1:z≠1:=by intro he;have hh:=h.involution;simp[he] at hh
  have ht1:m.t≠1:=by intro he;have hh:=m.t_order;simp[he] at hh
  have hzt1:z*m.t≠1:=by
    intro he
    have htzi:m.t=z⁻¹:=eq_inv_of_mul_eq_one_right he
    have hh:=hS4
    change Nat.card (zpowers z⊔zpowers m.t:Subgroup G)=4 at hh
    rw[htzi,zpowers_inv,sup_idem,Nat.card_zpowers,h.involution] at hh
    omega
  have hc:Nat.card (Subgroup.centralizer (U:Set G)⊓centralizer z:Subgroup G)=36:=by
    rw[inf_comm]
    exact (R.reflected_line_local_centralizer_product h P m ht hs hlocal).2
  let M:=normalizer (A:Set G)
  let N:=normalizer (U.subgroupOf M:Set M)
  obtain ⟨_,_,_,horb⟩:=R.plane_cubic_normalizer_data h A hA U m.common_fixed_card hfixed.2.1 hfixed.2.2
  have hNg:N.map M.subtype≤normalizer (U:Set G):=by
    have hh:=(U.subgroupOf M).le_normalizer_map M.subtype
    rwa[map_subgroupOf_eq_of_le hfixed.2.1] at hh
  have htrans:∀s∈S,s≠1→∃w∈normalizer (U:Set G),w*z*w⁻¹=s:=by
    intro s hsS hs1
    let W:Sylow 3 N:=default
    obtain ⟨w,hw,he⟩:=horb W z s (hSplane.symm ▸ mem_sup_left (mem_zpowers z))
      (hSplane.symm ▸ hsS) hz1 hs1
    exact ⟨w,hNg (map_mono (map_subtype_le (W:Subgroup N)) hw),he⟩
  have hcommon:=four_fixed_centralizer_of_orbit U S V hS4 hSV hSC hVC z
    (mem_sup_left (mem_zpowers z)) hz1 hc
    (fun s hs hs1=>reflected_four_kernel_fixed_card h P m s hs hs1) htrans
  have hcontrol:normalizer (U:Set G)⊓normalizer (S:Set G)≤normalizer (V:Set G):=
    normalizer_four_centralizers_le V S U (IsPGroup.of_card (n:=4) hV81) hV81 hS4 hSV hVC
      z m.t (mem_sup_left (mem_zpowers z)) (mem_sup_right (mem_zpowers m.t))
      (h.involution ▸ pow_orderOf_eq_one z) (m.t_order ▸ pow_orderOf_eq_one m.t)
      m.zt_commute hz1 ht1 hzt1 hcommon
  refine ⟨hcontrol,?_⟩
  apply le_trans (le_inf inf_le_right ?_) hcontrol
  rw[←hSplane]
  exact (le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer U))).trans
    inf_normalizer_le_normalizer_inf
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
