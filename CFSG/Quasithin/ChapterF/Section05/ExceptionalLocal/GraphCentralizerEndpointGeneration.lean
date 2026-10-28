module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionResidualJoin
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerNoPSL
public import Theory.GroupAction.MaximalCosetOrbit
/-!
# Generating the endpoint join from the centralizer residual and root

The literal ordinary upper group maps into both ordinary endpoints. Thus
the dihedral join U lies in each graph-fixed endpoint Dᵢ. Any subgroup K
containing U and the endpoint A₄ residual has intersection with Dᵢ of order
divisible by lcm(8,12)=24. Since |Dᵢ|=48, a root outside K forces that
intersection to have index two, and generates Dᵢ together with it.

The source specialization gives D ≤ O²(C_G(f))⟨z⟩. The independent residual
equality supplies the reverse inclusion. The actual maps, root, and extra
premises are retained throughout; no abstract endpoint placement is assumed.
Source: Aschbacher–Smith F.5.5, printed p.302.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

theorem sourceOrdinaryUpper_le_ordinary_range (b : Bool) :
    sourceOrdinaryUpper c i≤(ordinaryMap c i b).range := by
  rintro _ ⟨a,rfl⟩
  cases b
  · exact ⟨⟨a.val,(projectiveSylow_le_parabolics 1 hn).1 a.property⟩,rfl⟩
  · refine ⟨⟨a.val,(projectiveSylow_le_parabolics 1 hn).2 a.property⟩,?_⟩
    change i (c.right _) = i (c.middle _)
    rw [DFunLike.congr_fun c.compatible]
    rfl

variable [Finite G]

theorem sourceResidualJoin_le_Dendpoint (hi : Function.Injective i) (b : Bool) :
    sourceResidualJoin c i≤Dendpoint c i b := by
  rw [Dendpoint_eq_range_inf_C c i hi b]
  exact le_inf ((sourceResidualJoin_le_ordinary c i hi).trans
    (sourceOrdinaryUpper_le_ordinary_range c i b)) (sourceResidualJoin_le_C c i)

theorem source_root_mem_Dendpoint (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
    (b : Bool) : rootElement c i z∈Dendpoint c i b := by
  rw [Dendpoint_eq_range_inf_C c i h.embedding_injective b]
  constructor
  · cases b
    · exact ⟨z,rfl⟩
    · exact ⟨planeParameterMap (Multiplicative.ofAdd (longParameter F σ)),
        (source_root_eq_planeParameter c i z h).symm⟩
  · exact mem_centralizer_singleton_iff.mpr (source_graph_commutes_root c i z h).eq.symm

omit [Finite G] in
theorem source_Dendpoint_card (hi : Function.Injective i) (b : Bool) :
    Nat.card (Dendpoint c i b)=48 := by
  rw [Nat.card_congr (source_Dendpoint_equiv c i hi b).toEquiv,Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

theorem source_Dendpoint_residual_card (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
    (b : Bool) : Nat.card (pResidual 2 (Dendpoint c i b))=12 := by
  rw [Nat.card_congr (sourceEndpointResidualEquiv c i z h b).toEquiv,nat_card_alternatingGroup]
  norm_num

omit [Finite G] in
private theorem endpoint_residual_le_centralizer_residual (b : Bool) :
    (pResidual 2 (Dendpoint c i b)).map (Dendpoint c i b).subtype≤
      (pResidual 2 (C c i)).map (C c i).subtype := by
  rintro _ ⟨x,hx,rfl⟩
  let j : Dendpoint c i b →* C c i := inclusion ((Dendpoint_le_E c i b).trans inf_le_right)
  exact ⟨j x,map_pResidual_le 2 j (mem_map_of_mem j hx),rfl⟩

/-- The two endpoint input sizes force an index-two intersection with K. -/
theorem source_Dendpoint_le_sup_root (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
    (K : Subgroup G) (hUK : sourceResidualJoin c i≤K)
    (hres : ∀b, (pResidual 2 (Dendpoint c i b)).map (Dendpoint c i b).subtype≤K)
    (hzK : rootElement c i z∉K) (b : Bool) :
    Dendpoint c i b≤K⊔zpowers (rootElement c i z) := by
  let X := Dendpoint c i b⊓K
  have hUX : sourceResidualJoin c i≤X := le_inf
    (sourceResidualJoin_le_Dendpoint c i h.embedding_injective b) hUK
  have hresX : (pResidual 2 (Dendpoint c i b)).map (Dendpoint c i b).subtype≤X :=
    le_inf (map_subtype_le _) (hres b)
  have hUcard : Nat.card (sourceResidualJoin c i)=8 := by
    rw [Nat.card_congr (sourceResidualJoinEquiv c i h.embedding_injective).toEquiv,
      Nat.card_eq_fintype_card,DihedralGroup.card]
  have h8 : 8∣Nat.card X := hUcard ▸ card_dvd_of_le hUX
  have h12 : 12∣Nat.card X := by
    have hh := card_dvd_of_le hresX
    rwa [card_map_of_injective (Dendpoint c i b).subtype_injective,
      source_Dendpoint_residual_card c i z h b] at hh
  have h24 : 24∣Nat.card X := by simpa only [show Nat.lcm 8 12=24 from rfl] using Nat.lcm_dvd h8 h12
  have hX24 : 24≤Nat.card X := Nat.le_of_dvd Nat.card_pos h24
  have hcount : Nat.card X * X.relIndex (Dendpoint c i b)=48 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) X (Dendpoint c i b) bot_le
      (show X≤Dendpoint c i b from inf_le_left)
    simpa only [relIndex_bot_left,source_Dendpoint_card c i h.embedding_injective b] using hh
  have hnot1 : X.relIndex (Dendpoint c i b)≠1 := by
    intro hh
    exact hzK (((relIndex_eq_one.mp hh) (source_root_mem_Dendpoint c i z h b)).2)
  have hidx : X.relIndex (Dendpoint c i b)=2 := by
    have hpos : 0<X.relIndex (Dendpoint c i b) := by nlinarith
    have hle : X.relIndex (Dendpoint c i b)≤2 := by nlinarith
    omega
  have hgen : X⊔zpowers (rootElement c i z)=Dendpoint c i b :=
    sup_zpowers_eq_of_relIndex_prime inf_le_left Nat.prime_two hidx
      (source_root_mem_Dendpoint c i z h b) (fun hx=>hzK hx.2)
  rw [←hgen]
  exact sup_le_sup_right inf_le_right _

/-- Actual residual specialization: each endpoint is generated by its residual
intersection and the literal root outside that residual. -/
theorem source_Dendpoint_le_residual_sup_root (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (hz : rootElement c i z∉(pResidual 2 (C c i)).map (C c i).subtype) (b : Bool) :
    Dendpoint c i b≤(pResidual 2 (C c i)).map (C c i).subtype⊔
      zpowers (rootElement c i z) :=
  source_Dendpoint_le_sup_root c i z h _ (sourceResidualJoin_le_twoResidual c i)
    (endpoint_residual_le_centralizer_residual c i) hz b

/-- The endpoint join equals the actual centralizer residual supplemented by
its literal root, once the independently produced residual equality is known. -/
theorem source_D_eq_residual_sup_root (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (hres : DtwoResidual c i=(pResidual 2 (C c i)).map (C c i).subtype)
    (hz : rootElement c i z∉(pResidual 2 (C c i)).map (C c i).subtype) :
    D c i=(pResidual 2 (C c i)).map (C c i).subtype⊔zpowers (rootElement c i z) := by
  apply le_antisymm
  · exact sup_le (source_Dendpoint_le_residual_sup_root c i z h hz false)
      (source_Dendpoint_le_residual_sup_root c i z h hz true)
  · apply sup_le
    · rw [←hres]
      exact map_subtype_le _
    · exact zpowers_le.mpr ((show Dendpoint c i false≤D c i from le_sup_left)
        (source_root_mem_Dendpoint c i z h false))

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
