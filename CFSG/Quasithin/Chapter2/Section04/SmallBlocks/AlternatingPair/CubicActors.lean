module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Base
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.CubicNormalizer
public import Theory.GroupTheory.SylowNormalizerCommutingFamily.FactorControl
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Cubic actors in the original paired alternating-five configuration

The normalizer in the minimal parabolic of a Sylow two-subgroup of the
normal block join is proper and contains the marked Sylow subgroup. The
unique maximal-overgroup property therefore puts this normalizer inside
`M`. Normalizer control for commuting factors places a block Sylow
normalizer there, yielding a cubic element of the original block. The
marked exchanging element supplies a commuting cubic in the second block.
Each cubic generates its entire block through commutators.

Source: Aschbacher–Smith, proof of 2.4.25, printed p.542; this supplies the
original cubic actors used in the argument that only one component projection
of `L` is nontrivial.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {H : Type*} [Group H] [Finite H]

private theorem exists_cubic_in_unique_maximal
    (S : Sylow 2 H) (B J K L : Subgroup H) [J.Normal]
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (hSB : (S : Subgroup H) ≤ B) (hB : IsCoatom B)
    (hgen : K ⊔ L = J) (hcomm : L ≤ centralizer (K : Set H))
    (hK : IsAlternatingBlock K 5) :
    ∃ a : H, a ∈ B ⊓ K ∧ orderOf a = 3 ∧ ⁅K,zpowers a⁆ = K := by
  have hKJ : K ≤ J := le_sup_left.trans_eq hgen
  have hLJ : L ≤ J := le_sup_right.trans_eq hgen
  let C : Bool → Subgroup J := fun b => if b then K.subgroupOf J else L.subgroupOf J
  have hc : Pairwise (fun i j => C i ≤ centralizer (C j : Set J)) := by
    intro i j hij
    cases i <;> cases j <;> try exact (hij rfl).elim
    · intro x hx y hy
      exact Subtype.ext (hcomm hx y hy)
    · intro x hx y hy
      exact Subtype.ext ((le_centralizer_iff.mp hcomm) hx y hy)
  have hCg : iSup C = ⊤ := by
    rw [iSup_bool_eq]
    change K.subgroupOf J ⊔ L.subgroupOf J = ⊤
    rw [←subgroupOf_sup hKJ hLJ,hgen,subgroupOf_self]
  obtain ⟨P,hP⟩ := S.exists_sylow_map_eq_inf_of_normal J
  obtain ⟨R,hR,hnR⟩ := P.factor_normalizer_control C hc hCg true
  have hKC : IsAlternatingBlock (C true) 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
      (subgroupOfEquivOfLe hKJ).symm hK
  let N := normalizer ((P : Subgroup J).map J.subtype : Set H)
  have hSN : (S : Subgroup H) ≤ N := by
    dsimp only [N]
    rw [hP]
    exact (le_inf (S : Subgroup H).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hN : N ≠ ⊤ := by
    intro he
    let : ((P : Subgroup J).map J.subtype).Normal := normalizer_eq_top_iff.mp he
    have hPN : (P : Subgroup J).Normal := by
      have hh : (((P : Subgroup J).map J.subtype).comap J.subtype).Normal := inferInstance
      simpa only [comap_map_eq_self_of_injective J.subtype_injective] using hh
    let := hPN
    have hRN : (R : Subgroup (C true)).Normal := by
      rw [hR]
      infer_instance
    exact hKC.sylow_normalizer_ne_top_five R (normalizer_eq_top_iff.mpr hRN)
  have hNB : N ≤ B := hu.le_maximal ⟨hSB,hB.covBy_top⟩ hSN (lt_top_iff_ne_top.mpr hN)
  obtain ⟨r,hr,hr3⟩ := hKC.exists_sylow_normalizer_cubic R
  let f : C true →* H := J.subtype.comp (C true).subtype
  have hf : Function.Injective f := J.subtype_injective.comp (C true).subtype_injective
  have hfrange : (⊤ : Subgroup (C true)).map f = K := by
    rw [←map_map,←MonoidHom.range_eq_map,range_subtype]
    exact map_subgroupOf_eq_of_le hKJ
  have hrN : f r ∈ N := (P : Subgroup J).le_normalizer_map J.subtype
    (mem_map_of_mem J.subtype (hnR (mem_map_of_mem (C true).subtype hr)))
  refine ⟨f r,⟨hNB hrN,?_⟩,(orderOf_injective f hf r).trans hr3,?_⟩
  · exact hfrange ▸ mem_map_of_mem f (mem_top r)
  · have hh := congrArg (Subgroup.map f) (hKC.commutator_cubic_eq_top r hr3)
    simpa only [map_commutator,hfrange,MonoidHom.map_zpowers] using hh

variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

/-- Two actual commuting cubic actors in the original maximal-local intersections. -/
theorem AlternatingPairSourceSetup.cubic_actors
    (c : AlternatingPairSourceSetup d M₀) :
    ∃ a b : G,
      a ∈ M ⊓ d.block.map d.H.subtype ∧ b ∈ M ⊓ c.second ∧
      orderOf a = 3 ∧ orderOf b = 3 ∧ Commute a b ∧
      ⁅d.block.map d.H.subtype,zpowers a⁆ = d.block.map d.H.subtype ∧
      ⁅c.second,zpowers b⁆ = c.second := by
  let L₂ := c.second.subgroupOf d.H
  have hL₂H : c.second ≤ d.H := c.join ▸ (le_sup_right : c.second ≤ d.block.map d.H.subtype ⊔ c.second)
    |>.trans (map_subtype_le d.L0)
  have hgen : d.block ⊔ L₂ = d.L0 := by
    apply map_injective d.H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hL₂H]
    exact c.join
  have hc : L₂ ≤ centralizer (d.block : Set d.H) := by
    intro x hx y hy
    exact Subtype.ext (c.commutes hx y (mem_map_of_mem d.H.subtype hy))
  have hB : IsAlternatingBlock d.block 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
      (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm c.marked₁.block
  let := d.L0_normal
  have hSM : (d.S : Subgroup d.H) ≤ M.subgroupOf d.H := by
    intro x hx
    exact d.full_pair.1.1.2.1 (mem_map_of_mem d.H.subtype hx)
  obtain ⟨a,ha,ha3,hac⟩ := exists_cubic_in_unique_maximal d.S (M.subgroupOf d.H)
    d.L0 d.block L₂ d.minimal_parabolic.1 hSM d.intersection_maximal hgen hc hB
  have haK : (a : G) ∈ d.block.map d.H.subtype := mem_map_of_mem d.H.subtype ha.2
  have haM : (a : G) ∈ M := ha.1
  have ha3G : orderOf (a : G) = 3 := (orderOf_injective d.H.subtype d.H.subtype_injective a).trans ha3
  have hacG : ⁅d.block.map d.H.subtype,zpowers (a : G)⁆ = d.block.map d.H.subtype := by
    have hh := congrArg (Subgroup.map d.H.subtype) hac
    simpa only [map_commutator,MonoidHom.map_zpowers,Subgroup.coe_subtype] using hh
  obtain ⟨t,ht,he⟩ := c.exchange
  let e := MulAut.conj t
  change (d.block.map d.H.subtype).map e.toMonoidHom = c.second at he
  have htM := d.full_pair.1.1.2.1 ht
  have hbM : e (a : G) ∈ M := M.mul_mem (M.mul_mem htM haM) (M.inv_mem htM)
  have hbL : e (a : G) ∈ c.second := he ▸ mem_map_of_mem e.toMonoidHom haK
  refine ⟨a,e (a : G),⟨haM,haK⟩,⟨hbM,hbL⟩,ha3G,?_,?_,hacG,?_⟩
  · exact (e.orderOf_eq (a : G)).trans ha3G
  · exact c.commutes hbL a haK
  · have hh := congrArg (Subgroup.map e.toMonoidHom) hacG
    simpa only [map_commutator,MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom,he] using hh

end CFSG.Quasithin.Chapter2
