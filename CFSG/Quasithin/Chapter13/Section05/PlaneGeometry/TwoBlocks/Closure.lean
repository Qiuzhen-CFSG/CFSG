module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourcePair
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Normalizer
public import Theory.GroupTheory.PResidual.CoprimeKernelJoin.Normalizer

/-!
# The original normalizer's full cubic residual

The preimage of the native cubic pair is O₂(L)P. Its intrinsic cubic
residual is VP, since [O₂(L),L]=V. Full-M conjugation preserves that
preimage, so VP is normal in the original N_M(W). The centerless A₄²
outer-index argument at three-rank two identifies VP with the entire
O^{3′}(N_M(W)); factors of other odd orders are allowed and disappear.

Source: Aschbacher–Smith13.5.6, printed p.917.
-/

public section
open Subgroup BinaryPermutation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)

theorem CubicPair.normalized {W:Subgroup G} (c:CubicPair d W)
    (hb:ChapterC.IsAlternatingBlock L 6) (hU:(ChapterC.blockU L).map L.subtype=V)
    (hMV:M≤normalizer (V:Set G)) (hWV:W≤V) :
    M⊓normalizer (W:Set G)≤normalizer ((V⊔(c.first⊔c.second).map L.subtype : Subgroup G):Set G) := by
  let P:=(c.first⊔c.second).map L.subtype
  let Q:=(pCore 2 L).map L.subtype
  have hVQ:V≤Q:=by rw [←hU];exact map_mono ChapterC.blockU_le_core
  have hVn:Q⊔P≤normalizer (V:Set G):=
    (sup_le (map_subtype_le _) (map_subtype_le _)).trans
      (le_sup_left.trans d.normalizes_V)
  have hc:⁅P,Q⁆≤V:=by
    rw [←hU,ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype,commutator_comm P Q]
    exact commutator_mono le_rfl (map_subtype_le _)
  have hcop:Nat.Coprime 3 (Nat.card Q):=by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p:=2) (G:=L)).map L.subtype |>.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hg:primeToResidual 3 (V⊔P : Subgroup G)=⊤:=by
    obtain ⟨e⟩:=c.product
    apply (map_injective (f:=e.toMonoidHom) e.injective)
    rw [map_primeToResidual,AlternatingFourPair.pair_threeResidual,map_top_of_surjective _ e.surjective]
  have hr:(((c.first⊔c.second).map (localMap d)).comap (localMap d)).map L.subtype=Q⊔P:=by
    rw [comap_map_eq,localMap_kernel d hb,Subgroup.map_sup]
    exact sup_comm _ _
  have hN:=plane_normalizes_preimage d hMV W hWV _ c.image_normalized
  rw [hr] at hN
  exact hN.trans (normalizer_join_of_coprime_kernel 3 Q V P hVQ hVn hc hcop hg)

theorem CubicPair.le_plane_normalizer {W:Subgroup G} (c:CubicPair d W)
    (hU:(ChapterC.blockU L).map L.subtype=V) (hWV:W≤V) :
    V⊔(c.first⊔c.second).map L.subtype≤M⊓normalizer (W:Set G) := by
  have hVL:V≤L:=by rw [←hU];exact map_subtype_le _
  have hLM:L≤M:=by rw [d.local_normalizer];exact L.le_normalizer
  let := Section07.NaturalAction.elementary d
  have hVW:V≤centralizer (W:Set G):=by
    intro v hv w hw
    exact congrArg Subtype.val (mul_comm' (⟨w,hWV hw⟩:V) ⟨v,hv⟩)
  apply le_inf
  · exact sup_le (hVL.trans hLM) ((map_subtype_le _).trans hLM)
  · exact sup_le (hVW.trans (Subgroup.centralizer_le_normalizer _))
      (normalizes_plane_of_localMap_stabilizes d _ W hWV c.image_stabilizes)

theorem CubicPair.residual_eq {W:Subgroup G} (c:CubicPair d W)
    (hb:ChapterC.IsAlternatingBlock L 6) (hU:(ChapterC.blockU L).map L.subtype=V)
    (hMV:M≤normalizer (V:Set G)) (hWV:W≤V)
    (hr:primeRank 3 (M⊓normalizer (W:Set G) : Subgroup G)≤2) :
    (primeToResidual 3 (M⊓normalizer (W:Set G) : Subgroup G)).map (M⊓normalizer (W:Set G)).subtype=
      V⊔(c.first⊔c.second).map L.subtype := by
  let N:=M⊓normalizer (W:Set G)
  let X:=V⊔(c.first⊔c.second).map L.subtype
  have hXN:X≤N:=CubicPair.le_plane_normalizer d c hU hWV
  let : (X.subgroupOf N).Normal:=normal_subgroupOf_of_le_normalizer (CubicPair.normalized d c hb hU hMV hWV)
  obtain ⟨e⟩:=c.product
  have he:=AlternatingFourPair.residual_eq_of_normal_pair (X.subgroupOf N)
    ((subgroupOfEquivOfLe hXN).trans e) hr
  rw [he,map_subgroupOf_eq_of_le hXN]
end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
