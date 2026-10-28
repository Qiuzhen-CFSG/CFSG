module
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.Source
public import Theory.GroupAction.DisjointCubicAutomorphisms
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Splitting.Residual

/-!
# The terminal independent-action contradiction

The original residual O²(C_K(t)) is A₄ and lies in H = O²(C_G(E)). The
source terminal recognition proves that M₁ centralizes H. A cubic element
of this residual therefore acts on B fixing B∩M₁ pointwise and preserving
B∩M₂. Its conjugate by the marked swap acts with the opposite support.
Both actions are nontrivial: C_G(B)=B is a two-group. The two cubic actions
then force nine to divide |K|=1920, a contradiction.

The coordinate argument uses only the literal two S₄ factors and their
trivial centers. It avoids choosing either of the two four-point fusion
alternatives and repairs the final source argument without the incorrect
printed Delta5 product assertion.

Source: Aschbacher--Smith, Theorem 13.9.1, printed pp.969--974, especially
the terminal construction on pp.973--974.
-/

public section
open Subgroup SymmetricFourWreath
namespace CFSG.Quasithin.Chapter13.Section09.Marking
variable {G:Type*} [Group G] {d:Configuration G} (m:Marking d)

private theorem native_center (a:D8) (h:∀c:S4,c*square a=square a*c) : a=1 :=
  (by decide : ∀a:D8,(∀c:S4,c*square a=square a*c)→a=1) a h

private theorem factors_commute (i j:C2) (hij:i≠j) :
    m.factor i≤centralizer (m.factor j:Set G) := by
  rintro x ⟨_,⟨a,rfl⟩,rfl⟩
  rw [mem_centralizer_iff]
  rintro y ⟨_,⟨b,rfl⟩,rfl⟩
  exact ((SymmetricFourWreath.factor_commute hij a b).map m.embedding).eq.symm

private theorem base_centralizer_first (a b:D8)
    (h:m.baseProductEmbedding (a,b)∈centralizer (m.factor 1:Set G)) : a=1 := by
  apply native_center
  intro c
  have hc:=mem_centralizer_iff.mp h (m.embedding (SymmetricFourWreath.factor 1 c))
    (mem_map_of_mem _ ⟨c,rfl⟩)
  change m.embedding (SymmetricFourWreath.factor 1 c)*m.embedding (sylowEmbedding (pair (a,b)))=
    m.embedding (sylowEmbedding (pair (a,b)))*m.embedding (SymmetricFourWreath.factor 1 c) at hc
  rw [←map_mul,←map_mul] at hc
  have hh:=congrArg (fun w:W=>w.left 1) (m.embedding_injective hc)
  simpa [SymmetricFourWreath.factor,sylowEmbedding,pair] using hh

private theorem base_centralizer_second (a b:D8)
    (h:m.baseProductEmbedding (a,b)∈centralizer (m.factor turn:Set G)) : b=1 := by
  apply native_center
  intro c
  have hc:=mem_centralizer_iff.mp h (m.embedding (SymmetricFourWreath.factor turn c))
    (mem_map_of_mem _ ⟨c,rfl⟩)
  change m.embedding (SymmetricFourWreath.factor turn c)*m.embedding (sylowEmbedding (pair (a,b)))=
    m.embedding (sylowEmbedding (pair (a,b)))*m.embedding (SymmetricFourWreath.factor turn c) at hc
  rw [←map_mul,←map_mul] at hc
  have hh:=congrArg (fun w:W=>w.left turn) (m.embedding_injective hc)
  simpa [SymmetricFourWreath.factor,sylowEmbedding,pair,turn_ne_one] using hh

private theorem B_centralizer_first :
    m.B⊓centralizer (m.factor 1:Set G)=m.B⊓m.factor turn := by
  apply le_antisymm
  · intro x hx
    have hxJ:=(map_mono (elementary_le_J false false) : m.B≤m.dihedralBase) hx.1
    change x∈m.dihedralBase at hxJ
    rw [←m.range_baseProductEmbedding] at hxJ
    obtain ⟨⟨a,b⟩,rfl⟩:=hxJ
    exact ⟨hx.1,((m.baseProductEmbedding_mem_second a b).mpr
      (m.base_centralizer_first a b hx.2)).2⟩
  · exact inf_le_inf_left _ (m.factors_commute turn 1 turn_ne_one)

private theorem B_centralizer_second :
    m.B⊓centralizer (m.factor turn:Set G)=m.B⊓m.factor 1 := by
  apply le_antisymm
  · intro x hx
    have hxJ:=(map_mono (elementary_le_J false false) : m.B≤m.dihedralBase) hx.1
    change x∈m.dihedralBase at hxJ
    rw [←m.range_baseProductEmbedding] at hxJ
    obtain ⟨⟨a,b⟩,rfl⟩:=hxJ
    exact ⟨hx.1,((m.baseProductEmbedding_mem_first a b).mpr
      (m.base_centralizer_second a b hx.2)).2⟩
  · exact inf_le_inf_left _ (m.factors_commute 1 turn turn_ne_one.symm)

private theorem B_factor_sup : (m.B⊓m.factor 1)⊔(m.B⊓m.factor turn)=m.B := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro x hx
  have hxJ:=(map_mono (elementary_le_J false false) : m.B≤m.dihedralBase) hx
  change x∈m.dihedralBase at hxJ
  rw [←m.range_baseProductEmbedding] at hxJ
  obtain ⟨⟨a,b⟩,rfl⟩:=hxJ
  obtain ⟨ha,hb⟩:=(m.elementaryGroup_coordinate a b false false).mp hx
  have h1:m.baseProductEmbedding (a,1)∈m.B⊓m.factor 1 :=
    ⟨(m.elementaryGroup_coordinate a 1 false false).mpr ⟨ha,(plane false).one_mem⟩,
      ((m.baseProductEmbedding_mem_first a 1).mpr rfl).2⟩
  have h2:m.baseProductEmbedding (1,b)∈m.B⊓m.factor turn :=
    ⟨(m.elementaryGroup_coordinate 1 b false false).mpr ⟨(plane false).one_mem,hb⟩,
      ((m.baseProductEmbedding_mem_second 1 b).mpr rfl).2⟩
  simpa only [←map_mul,Prod.mk_mul_mk,mul_one,one_mul] using
    ((m.B⊓m.factor 1)⊔(m.B⊓m.factor turn)).mul_mem (mem_sup_left h1) (mem_sup_right h2)

private theorem cubic_pair_false [Finite G] {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (a b:G) (haK:a∈normalizer (m.B:Set G)) (hbK:b∈normalizer (m.B:Set G))
    (ha:orderOf a=3) (hb:orderOf b=3)
    (haC:a∈centralizer (m.factor 1:Set G))
    (hbC:b∈centralizer (m.factor turn:Set G)) : False := by
  let f:=m.B.normalizerMonoidHom
  let x:f.range:=f.rangeRestrict ⟨a,haK⟩
  let y:f.range:=f.rangeRestrict ⟨b,hbK⟩
  let L:Subgroup m.B:=(m.B⊓m.factor 1).subgroupOf m.B
  let R:Subgroup m.B:=(m.B⊓m.factor turn).subgroupOf m.B
  have hgen:L⊔R=⊤ := by
    apply map_injective m.B.subtype_injective
    dsimp only [L,R]
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le inf_le_left,map_subgroupOf_eq_of_le inf_le_left,
      ←MonoidHom.range_eq_map,range_subtype,m.B_factor_sup]
  have hn (c:G) (hcK:c∈normalizer (m.B:Set G)) (hc:orderOf c=3) :
      f.rangeRestrict ⟨c,hcK⟩≠1 := by
    intro he
    have hk: (⟨c,hcK⟩:normalizer (m.B:Set G))∈f.ker :=
      congrArg Subtype.val he
    rw [normalizerMonoidHom_ker] at hk
    have hcB:c∈m.B := (m.centralizer_B (hG.evenCharacteristic d.T)) ▸ hk
    have hd:=orderOf_dvd_natCard (⟨c,hcB⟩:m.B)
    rw [orderOf_mk,hc,m.card_elementaryGroup false false] at hd
    norm_num at hd
  have hx3:x^3=1 := by
    apply Subtype.ext
    change f ⟨a,haK⟩^3=1
    rw [←map_pow]
    have he:(⟨a,haK⟩:normalizer (m.B:Set G))^3=1 :=
      Subtype.ext (ha ▸ pow_orderOf_eq_one a)
    rw [he,map_one]
  have hy3:y^3=1 := by
    apply Subtype.ext
    change f ⟨b,hbK⟩^3=1
    rw [←map_pow]
    have he:(⟨b,hbK⟩:normalizer (m.B:Set G))^3=1 :=
      Subtype.ext (hb ▸ pow_orderOf_eq_one b)
    rw [he,map_one]
  have h9:¬9∣Nat.card f.range := by
    intro hd
    have hh:=hd.trans (card_range_dvd f)
    rw [m.normalizer_card_1920 hG] at hh
    norm_num at hh
  have h:=MulAut.eq_one_or_eq_one_of_disjoint_cubic_actions f.range L R hgen x y hx3 hy3 h9
    (fun v hv=>by
      apply Subtype.ext
      change a*(v:G)*a⁻¹=(v:G)
      rw [←mem_centralizer_iff.mp haC v hv.2,mul_assoc,mul_inv_cancel,mul_one])
    (fun v hv=>by
      apply Subtype.ext
      change b*(v:G)*b⁻¹=(v:G)
      rw [←mem_centralizer_iff.mp hbC v hv.2,mul_assoc,mul_inv_cancel,mul_one])
    (fun v hv=>by
      have hvC:(v:G)∈centralizer (m.factor 1:Set G) :=
        (m.B_centralizer_first.symm ▸ (show (v:G)∈m.B⊓m.factor turn from hv)).2
      have hc:= (centralizer (m.factor 1:Set G)).mul_mem
        ((centralizer (m.factor 1:Set G)).mul_mem haC hvC)
        ((centralizer (m.factor 1:Set G)).inv_mem haC)
      change a*(v:G)*a⁻¹∈m.B⊓m.factor turn
      rw [←m.B_centralizer_first]
      exact ⟨(f ⟨a,haK⟩ v).property,hc⟩)
    (fun v hv=>by
      have hvC:(v:G)∈centralizer (m.factor turn:Set G) :=
        (m.B_centralizer_second.symm ▸ (show (v:G)∈m.B⊓m.factor 1 from hv)).2
      have hc:= (centralizer (m.factor turn:Set G)).mul_mem
        ((centralizer (m.factor turn:Set G)).mul_mem hbC hvC)
        ((centralizer (m.factor turn:Set G)).inv_mem hbC)
      change b*(v:G)*b⁻¹∈m.B⊓m.factor 1
      rw [←m.B_centralizer_second]
      exact ⟨(f ⟨b,hbK⟩ v).property,hc⟩)
  exact h.elim (hn a haK ha) (hn b hbK hb)

open FusionAlignment TerminalSubgroup in
include m in
/-- The terminal source subgroup forces two independent nontrivial cubic actions. -/
theorem terminal_cubic_contradiction [Finite G] {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) : False := by
  obtain ⟨hE,⟨eD⟩⟩:=m.source13_9_10 hG
  let D:=normalizerCentralizerResidual m.B m.t
  have hDcard:Nat.card D=12 := by
    rw [Nat.card_congr eD.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card,Nat.factorial]
  obtain ⟨a,ha⟩:=exists_prime_orderOf_dvd_card' (G:=D) 3 (by rw [hDcard];decide)
  have hDK:D≤normalizer (m.B:Set G) :=
    (residual_le (normalizerCentralizer m.B m.t)).trans inf_le_left
  have hDH:D≤terminal m.terminalFour :=
    residual_le_terminal_of_residual_centralizes m.terminalFour
      (normalizerCentralizer m.B m.t) (le_centralizer_iff.mp hE)
  have haC:(a:G)∈centralizer (m.factor 1:Set G) :=
    le_centralizer_iff.mp (m.source_terminal_psl3Two hG).2 (hDH a.property)
  have haG:orderOf (a:G)=3 := (orderOf_coe a).trans ha
  have hsK:=m.sylow_le_normalizer_B m.s_mem_sylow
  have hbK:m.s*(a:G)*m.s⁻¹∈normalizer (m.B:Set G) :=
    (normalizer (m.B:Set G)).mul_mem
      ((normalizer (m.B:Set G)).mul_mem hsK (hDK a.property))
      ((normalizer (m.B:Set G)).inv_mem hsK)
  have hb:orderOf (m.s*(a:G)*m.s⁻¹)=3 :=
    ((MulAut.conj m.s).orderOf_eq (a:G)).trans haG
  have hbC:m.s*(a:G)*m.s⁻¹∈centralizer (m.factor turn:Set G) := by
    rw [mem_centralizer_iff]
    rintro x ⟨_,⟨c,rfl⟩,rfl⟩
    have hh:= (show Commute (m.embedding (SymmetricFourWreath.factor 1 c)) (a:G) from
      mem_centralizer_iff.mp haC _ (mem_map_of_mem _ ⟨c,rfl⟩)).conj m.s
    simpa only [m.s_conjugates_factor, mul_one] using hh.eq
  exact m.cubic_pair_false hG (a:G) (m.s*(a:G)*m.s⁻¹) (hDK a.property) hbK haG hb haC hbC
end CFSG.Quasithin.Chapter13.Section09.Marking
