module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Control
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.FourLocal
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.FourNormalizer
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.OutsideCentralizers
/-!
# The full normalizer of the original reflected cubic

The local fixed-four normalizer has order72 and exhausts its global
normalizer, since the common centralizer has order12 and Aut(E4) has order6.
Its cubic orbit transports the marked involution centralizer to the other
two involutions of the four. Outside reflection centralizers have order36.
The original Sylow eight and these centralizers close the global normalizer
by the index-two strong-embedding contradiction. Thus N(U)=V N_M(U), and
the literal canonical V is normal in N(U).
Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
omit [Finite G] in
private theorem centralizer_conjugate_le (K I:Subgroup G) (w z:G) (hwK:w∈K) (hwI:w∈I)
    (hc:K⊓Subgroup.centralizer ({z}:Set G)≤I) :
    K⊓Subgroup.centralizer ({w*z*w⁻¹}:Set G)≤I:=by
  intro g hg
  let f:=MulAut.conj w
  have hgK:f.symm g∈K:=K.mul_mem (K.mul_mem (K.inv_mem hwK) hg.1) hwK
  have hgC:f.symm g∈Subgroup.centralizer ({z}:Set G):=by
    apply mem_centralizer_singleton_iff.mpr
    apply f.injective
    have hh: g*f z=f z*g:=mem_centralizer_singleton_iff.mp hg.2
    simpa only[map_mul,f.apply_symm_apply] using hh
  have hh:=hc ⟨hgK,hgC⟩
  have hm:=I.mul_mem (I.mul_mem hwI hh) (I.inv_mem hwI)
  change f (f.symm g)∈I at hm
  simpa only[f.apply_symm_apply] using hm

theorem reflected_line_global_normalizer (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (A:Subgroup G) (hA:A≤R.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16) (htA:m.t∈A)
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hTN:R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype)≤normalizer (A:Set G))
    (hlocal:centralizer z⊓normalizer
      ((((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)=
      centralizer z⊓normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
    let V:=CubicNormalizer.oddKernel X
    normalizer (U:Set G)=V⊔(normalizer (A:Set G)⊓normalizer (U:Set G)) ∧
      normalizer (U:Set G)≤normalizer (V:Set G) := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
  let V:=CubicNormalizer.oddKernel X
  let T:=R.cubicSylow X
  let S:=zpowers z⊔zpowers m.t
  let K:=normalizer (U:Set G)
  let L:=normalizer (A:Set G)⊓K
  let I:=V⊔L
  have hTK:T≤K:=by
    have he:T≤centralizer z⊓K:=by
      rw[hlocal]
      exact le_inf (inf_le_left.trans R.T_le_centralizer) inf_le_right
    exact he.trans inf_le_right
  have hTL:T≤L:=le_inf hTN hTK
  have hT8:Nat.card T=8:=R.cubicSylow_card h X (h.cubic_sylow_image_card P) (map_subtype_le _)
  let TS:Sylow 2 K:=((IsPGroup.of_card (p:=2) (n:=3) hT8).comap_subtype:IsPGroup 2 (T.subgroupOf K)).toSylow
    (R.cubicSylow_not_dvd_line_index h P m ht hs hlocal)
  have heS:T⊓Subgroup.centralizer (U:Set G)=S:=R.reflected_four_eq_sylow_fixed h P m ht hs
  have hSK:S≤K:=(heS ▸ inf_le_left).trans hTK
  have hS':(TS:Subgroup K)⊓(Subgroup.centralizer (U:Set G)).subgroupOf K=S.subgroupOf K:=by
    change (T⊓Subgroup.centralizer (U:Set G)).subgroupOf K=S.subgroupOf K
    rw[heS]
  have hS4:Nat.card ((TS:Subgroup K)⊓(Subgroup.centralizer (U:Set G)).subgroupOf K:Subgroup K)=4:=by
    rw[hS',Nat.card_congr (subgroupOfEquivOfLe hSK).toEquiv,(h.reflected_four P m).2]
  have hNI:normalizer ((((TS:Subgroup K)⊓(Subgroup.centralizer (U:Set G)).subgroupOf K):Subgroup K):Set K)≤I.subgroupOf K:=by
    rw[hS',←subgroupOf_normalizer_eq hSK]
    intro g hg
    have he:K⊓normalizer (S:Set G)=L:=R.reflected_four_normalizer_eq_local h P m A hA htA ht hs hlocal
    exact mem_sup_right (he ▸ (show (g:G)∈K⊓normalizer (S:Set G) from ⟨g.property,hg⟩))
  have hXV:X≤V:=by rw[←h.toCentralizerHypothesis.cubic_oddKernel_fixed X (h.cubic_sylow_image_card P) (map_subtype_le _)];exact inf_le_left
  have hZI:K⊓centralizer z≤I:=by
    rw[inf_comm,hlocal,R.cubic_local_normalizer_product h X (h.cubic_sylow_image_card P) (map_subtype_le _)]
    exact sup_le (hXV.trans le_sup_left) (hTL.trans le_sup_right)
  have hfix:=R.reflected_line_plane_position h P m A hA htA
  obtain ⟨_,_,_,horb⟩:=R.plane_cubic_ambient_data h A hA U m.common_fixed_card hfix.2.1 hfix.2.2
  have hSp:A⊓Subgroup.centralizer (U:Set G)=S:=R.reflected_four_eq_plane_fixed h P m A hA htA
  have hz1:z≠1:=by intro he;have hh:=h.involution;simp[he] at hh
  have hcent:∀x∈(TS:Subgroup K),orderOf x=2→Subgroup.centralizer ({x}:Set K)≤I.subgroupOf K:=by
    intro x hx hx2 g hg
    have hxT:(x:G)∈T:=hx
    have hxG:orderOf (x:G)=2:=(orderOf_injective K.subtype K.subtype_injective x).trans hx2
    have hgG:(g:G)∈K⊓Subgroup.centralizer ({(x:G)}:Set G):=⟨g.property,
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg))⟩
    by_cases hxS:(x:G)∈S
    · have hx1:(x:G)≠1:=by intro he;rw[he,orderOf_one] at hxG;omega
      obtain ⟨w,hw,he⟩:=horb z x (hSp.symm ▸ mem_sup_left (mem_zpowers z)) (hSp.symm ▸ hxS) hz1 hx1
      have hh:=centralizer_conjugate_le K I w z hw.2 (mem_sup_right hw) hZI
      rw[he] at hh
      exact hh hgG
    · exact (sup_le le_sup_left (hTL.trans le_sup_right))
        (R.outside_reflection_centralizer_le h P m ht hs hlocal x hxT hxG hxS hgG)
  have hzT:z∈T:=by
    have he:=R.cubicSylow_inf_core h X (h.cubic_sylow_image_card P) (map_subtype_le _)
    exact ((he.symm ▸ mem_zpowers z):z∈core z⊓R.cubicSylow X).2
  let zk:K:=⟨z,hTK hzT⟩
  let sk:K:=⟨m.s,hTK hs⟩
  have hKI:K≤I:=normalizer_le_of_card_three_four_centralizers U I m.common_fixed_card TS
    (fun x hx=>mem_sup_right (hTL hx)) hS4 hNI hcent zk sk hzT hs
    ((orderOf_injective K.subtype K.subtype_injective zk).symm.trans h.involution)
    ((orderOf_injective K.subtype K.subtype_injective sk).symm.trans m.s_order)
    (fun u hu=>mem_centralizer_singleton_iff.mp ((map_subtype_le _) hu.1)) m.s_not_centralizes_fixed
  let : IsElementaryAbelian 3 V:=(h.reflected_kernel_of_source_binary_normalizers P m).1
  have hVK:V≤K:=(show V≤Subgroup.centralizer (U:Set G) from fun a ha u hu=>
    congrArg Subtype.val (mul_comm' (⟨u,hXV hu.1⟩:V) (⟨a,ha⟩:V))).trans (centralizer_le_normalizer _)
  have hLN:L≤normalizer (V:Set G):=(R.reflected_four_normalizer_control h P m A hA htA ht hs hlocal).2
  exact ⟨le_antisymm hKI (sup_le hVK inf_le_right),hKI.trans (sup_le le_normalizer hLN)⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
