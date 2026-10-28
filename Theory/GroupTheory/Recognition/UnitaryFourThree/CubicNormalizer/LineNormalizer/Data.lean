module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Global
public import Theory.GroupTheory.NormalProductQuotientMap

/-!
# The original cubic-line normalizer quotient

The global normalizer is V times the actual local order72 subgroup. Its
intersection with V is the local three-core U. The original local S4 map
therefore induces a global S4 map with precisely the canonical kernel V,
and the literal relative index is24.
Source: Aschbacher, Sporadic Groups (1994),45.7(3),p.245.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem reflected_line_normalizer_data (R:RootPair z) (h:IsType z)
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
    let K:=normalizer (U:Set G)
    V≤K ∧ K≤normalizer (V:Set G) ∧ V.relIndex K=24 ∧
      ∃f:K→*Equiv.Perm (Fin 4),Function.Surjective f ∧ f.ker=V.subgroupOf K := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
  let V:=CubicNormalizer.oddKernel X
  let K:=normalizer (U:Set G)
  let L:=normalizer (A:Set G)⊓K
  have hglobal:=R.reflected_line_global_normalizer h P m A hA htA ht hs hTN hlocal
  have hprod:K=V⊔L:=hglobal.1
  have hKV:K≤normalizer (V:Set G):=hglobal.2
  have hVK:V≤K:=hprod ▸ le_sup_left
  have hfix:=R.reflected_line_plane_position h P m A hA htA
  obtain ⟨_,hcore,⟨f,hf,hker⟩,_⟩:=R.plane_cubic_ambient_data h A hA U m.common_fixed_card hfix.2.1 hfix.2.2
  have hXV:X≤V:=by rw[←h.toCentralizerHypothesis.cubic_oddKernel_fixed X (h.cubic_sylow_image_card P) (map_subtype_le _)];exact inf_le_left
  have hVp:IsPGroup 3 V:=IsPGroup.of_card (n:=4) (h.reflected_kernel_of_source_binary_normalizers P m).2
  have hInt:V.subgroupOf L=U.subgroupOf L:=by
    apply le_antisymm ?_ (comap_mono (inf_le_left.trans hXV))
    let : (V.subgroupOf L).Normal:=normal_subgroupOf_of_le_normalizer (inf_le_right.trans hKV)
    have hle:V.subgroupOf L≤pCore 3 L:=le_sSup ⟨inferInstance,hVp.comap_subtype⟩
    intro l hl
    change (l:G)∈U
    rw[←hcore]
    exact mem_map_of_mem L.subtype (hle hl)
  obtain ⟨ψ,hψ,hψker⟩:=surjection_of_normal_product K V L hVK inf_le_right hKV hprod f hf (hker.trans hInt.symm)
  refine ⟨hVK,hKV,?_,ψ,hψ,hψker⟩
  change (V.subgroupOf K).index=24
  rw[←hψker,index_ker,MonoidHom.range_eq_top.mpr hψ,card_top]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
