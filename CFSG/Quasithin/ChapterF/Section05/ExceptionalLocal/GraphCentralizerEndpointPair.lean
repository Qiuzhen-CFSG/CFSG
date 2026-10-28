module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerSymmetric
public import Theory.SpecificGroups.SymmetricSix.Parabolics.EndpointInvolutions
/-!
# The original fixed-endpoint involution pair

The common dihedral group U has order eight and lies in the centralizer
residual. The original root centralizes U and lies outside that residual,
so U⟨z⟩ has order sixteen and lies in both endpoints. After identifying
D with S₆, the two order-48 endpoints are its incident parabolics. Their
explicit involutions transport back through the literal subgroup inclusion.

This discharges the endpoint-pair premise of the F.4.26 completion
recognition used in F.5.5, printed p.302.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_common_rootJoin_card (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Nat.card (sourceResidualJoin c i⊔zpowers (rootElement c i z):Subgroup G)=16 := by
  have hUcard : Nat.card (sourceResidualJoin c i)=8 := by
    rw [Nat.card_congr (sourceResidualJoinEquiv c i h.embedding_injective).toEquiv,
      Nat.card_eq_fintype_card,DihedralGroup.card]
  have hz2 : rootElement c i z ^2=1 := source_root_order c i z h ▸ pow_orderOf_eq_one _
  have hout : rootElement c i z∉sourceResidualJoin c i := fun hz =>
    source_root_not_mem_centralizer_residual c i z h R hR
      (sourceResidualJoin_le_twoResidual c i hz)
  have hnorm : rootElement c i z∈normalizer (sourceResidualJoin c i:Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro x hx
    have hxM : x∈M c i false :=
      (Dendpoint_le_E c i false (sourceResidualJoin_le_Dendpoint c i h.embedding_injective false hx)).1
    rw [←source_root_centralizer c i z h] at hxM
    exact mem_centralizer_singleton_iff.mp hxM
  rw [card_sup_zpowers_of_normalizing_involution _ _ hz2 hout hnorm,hUcard]

theorem source_common_rootJoin_le_Dendpoint (b:Bool) :
    sourceResidualJoin c i⊔zpowers (rootElement c i z)≤Dendpoint c i b :=
  sup_le (sourceResidualJoin_le_Dendpoint c i h.embedding_injective b)
    (zpowers_le.mpr (source_root_mem_Dendpoint c i z h b))

theorem source_fixed_endpoint_pair :
    ∃s t:G,s∈Dendpoint c i false ∧ t∈Dendpoint c i true ∧
      s∉Dendpoint c i false⊓Dendpoint c i true ∧
      t∉Dendpoint c i false⊓Dendpoint c i true ∧
      orderOf s=2 ∧ orderOf t=2 ∧ orderOf (s*t)=4 := by
  obtain ⟨S,hS⟩:=source_sylowImage_isSylow c i z h
  have hT:IsPGroup 2 (Source.sylowImage c i):=hS ▸ S.isPGroup'
  obtain ⟨R,hR⟩:=(show IsPGroup 2 (Tf c i) from hT.comap_subtype).exists_le_sylow
  obtain ⟨e⟩:=source_D_symmetric c i z h R hR
  let H := (Dendpoint c i false).subgroupOf (D c i)
  let K := (Dendpoint c i true).subgroupOf (D c i)
  let P := (sourceResidualJoin c i⊔zpowers (rootElement c i z)).subgroupOf (D c i)
  have hP : sourceResidualJoin c i⊔zpowers (rootElement c i z)≤D c i :=
    (source_common_rootJoin_le_Dendpoint c i z h false).trans (source_Dendpoint_le_D c i false)
  have hPcard : Nat.card P=16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv).trans (source_common_rootJoin_card c i z h R hR)
  have hcard (b:Bool) : Nat.card ((Dendpoint c i b).subgroupOf (D c i))=48 :=
    (Nat.card_congr (subgroupOfEquivOfLe (source_Dendpoint_le_D c i b)).toEquiv).trans
      (source_Dendpoint_card c i h.embedding_injective b)
  have hgen : H⊔K=⊤ := by
    rw [←subgroupOf_sup (source_Dendpoint_le_D c i false) (source_Dendpoint_le_D c i true)]
    exact subgroupOf_self _
  obtain ⟨s,t,hs,ht,hsout,htout,hs2,ht2,hst⟩:=
    Theory.SpecificGroups.SymmetricSix.pair_of_equiv_symmetricSix e H K P hPcard
      (hcard false) (hcard true)
      (subgroupOf_mono _ (source_common_rootJoin_le_Dendpoint c i z h false))
      (subgroupOf_mono _ (source_common_rootJoin_le_Dendpoint c i z h true)) hgen
  exact ⟨s.val,t.val,hs,ht,hsout,htout,
    (orderOf_injective (D c i).subtype (D c i).subtype_injective s).trans hs2,
    (orderOf_injective (D c i).subtype (D c i).subtype_injective t).trans ht2,
    (orderOf_injective (D c i).subtype (D c i).subtype_injective (s*t)).trans hst⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
