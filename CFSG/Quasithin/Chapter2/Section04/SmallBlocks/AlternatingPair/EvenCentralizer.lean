module
public import Theory.GroupTheory.EvenQuotientCentralizer
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.CubicComponent
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
/-! The opposite block's cubic lies in the actual ordinary component by the
rank-two residual theorem. It moves its elementary layer, which lies in SI
and centralizes the selected block. Its nontrivial displacement survives the
component's central two-core. Thus the faithful quotient block has even
centralizer, the exact input for an intrinsic normalizer Sylow to fix an
involution and hence select a guarded local overgroup.
Source: Aschbacher--Smith 2.4.25, printed pp.542--543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
variable {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.phi_component_even_centralizer
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    [IsQuasisimple D] (hz : center D = ⊥) (hr : 2 ≤ primeRank 3 D)
    (ho : IsPGroup 2 (MulAut.Outer D)) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
      SI S L ≤ normalizer (K.map GI.subtype : Set G) →
    ∀ e : (K ⧸ pCore 2 K) ≃* D,
    2 ∣ Nat.card (centralizer (((L.subgroupOf GI).subgroupOf K).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) : Set D)) := by
  intro S L GI K hK hLK hNK e
  let : IsQuasisimple K := hK.2
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e.symm
  have hzK : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro y hy
    exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨y,hy⟩).property)
  have hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by rwa [primeRank_congr 3 e]
  have hoK : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) :=
    ho.of_injective (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective
  have henv := c.phi_normalizer_source hG T hM hTM hu hST hSM hMT hi
  have hres : K = primeToResidual 3 GI :=
    hK.isCComponent.eq_primeToResidual_three_of_rank_outer_two hzK hrK
      ((hG.twoLocal_sqtk henv.2.1).stronglyQuasithin 3 Nat.prime_three (by decide)) hoK
  obtain ⟨a,b,_,hb,_,hb3,_,_,_⟩ := c.cubic_actors
  have hbG : b ∈ GI := Subgroup.centralizer_le_normalizer _
    (c.phi_intersection_centralized ⟨hb.1,c.join ▸ mem_sup_right hb.2⟩)
  let bG : GI := ⟨b,hbG⟩
  have hbG3 : orderOf bG=3 := (Subgroup.orderOf_coe bG).symm.trans hb3
  have hbK : bG ∈ K := by
    rw [hres]
    exact mem_primeToResidual_of_pow (n:=1)
      (by simpa only [pow_one,←hbG3] using pow_orderOf_eq_one bG)
  let k : K := ⟨bG,hbK⟩
  let U := sourceModule c.second
  have hUSI : U ≤ SI S L := le_inf
    (c.marked₂.module_le.trans inf_le_left)
    (c.marked₂.module_le.trans c.marked₁.normalizes)
  have hUSG : U ≤ GI := hUSI.trans
    ((normalizer_Phi_eq c.marked₁ c.marked₂).ge.trans inf_le_right)
  let V := U.subgroupOf GI
  have hVK : V ≤ normalizer (K : Set GI) := by
    intro u hu
    apply mem_normalizer_iff.mpr
    intro v
    have hh := mem_normalizer_iff.mp (hNK (hUSI hu)) (v:G)
    change GI.subtype v ∈ K.map GI.subtype ↔
      GI.subtype (u*v*u⁻¹) ∈ K.map GI.subtype at hh
    simpa only [mem_map_iff_mem GI.subtype_injective] using hh
  have hVL : V ≤ centralizer (L.subgroupOf GI : Set GI) := by
    intro u hu l hl
    exact Subtype.ext (c.commutes (map_subtype_le _ hu) l hl)
  have hV : IsElementaryAbelian 2 V := by
    let : IsElementaryAbelian 2 U := c.marked₂.block.2.1.elementary.map c.second.subtype
    exact IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hUSG).toMonoidHom
      (subgroupOfEquivOfLe hUSG).injective
  have hbn : bG ∈ normalizer (V : Set GI) := by
    have hbu : b ∈ normalizer (U : Set G) :=
      (normalizer_le_normalizer_characteristic_image c.second (blockU c.second))
        (c.second.le_normalizer hb.2)
    apply mem_normalizer_iff.mpr
    intro u
    exact mem_normalizer_iff.mp hbu u
  have hbnot : ¬ bG ∈ centralizer (V : Set GI) := by
    intro hh
    have hbu : (⟨b,hb.2⟩ : c.second) ∈ centralizer (blockU c.second : Set c.second) := by
      intro u hu
      have huU : (u:G) ∈ U := mem_map_of_mem c.second.subtype hu
      exact Subtype.ext (congrArg GI.subtype (hh ⟨u,hUSG huU⟩ huU))
    rw [c.marked₂.block.2.1.centralizer_blockU] at hbu
    have hp : (⟨⟨b,hb.2⟩,hbu⟩ : pCore 2 c.second)^3=1 :=
      Subtype.ext (Subtype.ext (hb3 ▸ pow_orderOf_eq_one b))
    have hone := (pCore_isPGroup.powEquiv (by decide : Nat.Coprime 2 3)).injective
      (show IsPGroup.powEquiv pCore_isPGroup (by decide : Nat.Coprime 2 3)
        (⟨⟨b,hb.2⟩,hbu⟩ : pCore 2 c.second) =
        IsPGroup.powEquiv pCore_isPGroup (by decide : Nat.Coprime 2 3) 1 from by
          simpa only [IsPGroup.powEquiv_apply,one_pow] using hp)
    have hb1 : b=1 := congrArg (fun x : pCore 2 c.second => ((x:c.second):G)) hone
    simp only [hb1,orderOf_one] at hb3
    omega
  exact even_quotient_centralizer_of_moved_elementary K (L.subgroupOf GI) V hLK
    hVK hVL hV k ((Subgroup.orderOf_coe k).symm.trans hbG3)
    (fun l hl => Subtype.ext (c.commutes hb.2 l hl)) hbnot hbn e
end CFSG.Quasithin.Chapter2
