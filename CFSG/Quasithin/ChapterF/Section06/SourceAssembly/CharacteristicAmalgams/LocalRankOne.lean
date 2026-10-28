module
public import Theory.GroupTheory.CenterFreeCubicFixedIndex
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalContext
public import Stellmacher.SectionNine.NineTwoLocalIndex
public import Stellmacher.SectionNine.NineTwoCoreNoncontainment
public import Stellmacher.SectionNine.NineThreeAssembly

/-!
# The cubic local form of Stellmacher (9.2)

When the initial vertex already has quotient S₃ over its two-core, the
index-two fixed-space argument determines its center module directly.
Two distinct Sylow fixed subgroups meet trivially because the initial
vertex is centerless by (7.5); their indices bound the module by four.
The local lower bound then gives equality. Conjugation transports the
same conclusion to every two-neighbor configuration of (9.2).

Unlike the general rank-one recognition proof, this cubic specialization
requires no ambient Hypothesis Two or commutator-center assertion (6.4).
Source: Stellmacher, Journal of Algebra 190 (1997), (9.2), printed p.48,
as used for genuine cubic Goldschmidt triples in Aschbacher–Smith F.6.5.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher Stellmacher.SectionsFiveToSeven Stellmacher.Later
open Stellmacher.SectionsFiveToSeven.CosetGraphContext
namespace Stellmacher.SectionNine.LocalCubic
universe u
variable {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}

/-- The initial cubic center is bounded by its index-two neighboring intersection. -/
theorem center_card_le_four_of_neighbor_index_two
    (h7 : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext.{u,u} G T A B) (cp : CriticalPath Γ)
    (e : ((stabilizer Γ cp.a) ⧸ pCore 2 (stabilizer Γ cp.a)) ≃* Equiv.Perm (Fin 3))
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (m : Γ.Vertex) (hm : m ∈ Neighborhood Γ cp.firstStep)
    (hindex : QuotientCardEq (ZAt Γ cp.a) (ZAt Γ cp.a ⊓ ZAt Γ m) 2)
    (hgenerate : QAt Γ m ⊔ (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) = GAt Γ cp.firstStep) :
    Nat.card (ZAt Γ cp.a) ≤ 4 := by
  have hnot := Stellmacher.SectionNine.nine_two_core_noncontainment h7 Γ cp m hm hgenerate
  obtain ⟨hUT,hnon,hne,hfixed⟩ :=
    Stellmacher.SectionNine.nine_two_fixed_index h7 Γ cp m hm hindex hnot
  let P := stabilizer Γ cp.a
  let V := (ZAt Γ cp.a).subgroupOf P
  let U := QAt Γ cp.firstStep ⊓ QAt Γ m
  have hTP : T ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  obtain ⟨_,S,hS⟩ := (SevenSix.edge_sylow_data h7 Γ cp).1
  have hS' : (S : Subgroup P) = (T).subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hTP]
    exact hS
  have hZP : ZAt Γ cp.a ≤ P := by
    exact (lemma_seven_three h7 Γ).center_core cp.a cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) |>.trans
      (SevenSix.omegaOneCenter_le_centerAmbient (q Γ cp.a)) |>.trans
      ((map_subtype_le (center (q Γ cp.a))).trans (by
        rw [q, Γ.twoCoreAt_def]
        exact map_subtype_le _))
  have hVnorm : V.Normal := (normal_subgroupOf_iff_le_normalizer hZP).mpr
    (stabilizer_le_normalizer_z Γ cp.a)
  let := hVnorm
  have hc : center P = ⊥ := (lemma_seven_five h7 Γ cp hcomm).start_center_trivial
  have hQ : (pCore 2 P).map P.subtype = QAt Γ cp.a := by
    exact (Γ.twoCoreAt_def cp.a).symm
  have hVQ : V ≤ centralizer (pCore 2 P : Set P) := by
    intro x hx y hy
    apply Subtype.ext
    have hz := (lemma_seven_four h7 Γ cp).edge_centralizer
    have hyQ : (y : G) ∈ q Γ cp.a := by
      change (y : G) ∈ QAt Γ cp.a
      rw [← hQ]
      exact mem_map_of_mem P.subtype hy
    rw [← hz] at hyQ
    exact hyQ.2 (x : G) hx |>.symm
  have hUS : U.subgroupOf P ≤ (S : Subgroup P) := by
    rw [hS']
    intro x hx
    exact hUT hx
  have hUnot : ¬ U.subgroupOf P ≤ pCore 2 P := by
    intro hh
    apply hnot
    intro x hx
    have hxp : x ∈ P := hTP (hUT hx)
    change x ∈ QAt Γ cp.a
    rw [← hQ]
    exact mem_map_of_mem P.subtype (hh (show (⟨x,hxp⟩ : P) ∈ U.subgroupOf P from hx))
  have hfixeq : V ⊓ centralizer (U.subgroupOf P : Set P) =
      (ZAt Γ cp.a ⊓ centralizer (U : Set G)).subgroupOf P := by
    ext x
    constructor
    · rintro ⟨hx,hcx⟩
      refine ⟨hx, ?_⟩
      intro y hy
      exact congrArg Subtype.val (hcx (⟨y,hTP (hUT hy)⟩ : P) hy)
    · rintro ⟨hx,hcx⟩
      refine ⟨hx, ?_⟩
      intro y hy
      exact Subtype.ext (hcx (y : G) hy)
  have hfixindex : (V ⊓ centralizer (U.subgroupOf P : Set P)).relIndex V = 2 := by
    rw [hfixeq]
    change ((ZAt Γ cp.a ⊓ centralizer (U : Set G)).subgroupOf P).relIndex
      ((ZAt Γ cp.a).subgroupOf P) = 2
    rw [relIndex_subgroupOf hZP]
    have hh := ((ZAt Γ cp.a ⊓ centralizer (U : Set G)).subgroupOf (ZAt Γ cp.a)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show ZAt Γ cp.a ⊓ centralizer (U : Set G) ≤ ZAt Γ cp.a from inf_le_left)).toEquiv] at hh
    change (ZAt Γ cp.a ⊓ centralizer (U : Set G)).relIndex (ZAt Γ cp.a) *
      Nat.card (ZAt Γ cp.a ⊓ centralizer (U : Set G) : Subgroup G) = Nat.card (ZAt Γ cp.a) at hh
    change Nat.card (ZAt Γ cp.a) = 2 * Nat.card (ZAt Γ cp.a ⊓ centralizer (U : Set G) : Subgroup G) at hfixed
    have hpos := Nat.card_pos (α := (ZAt Γ cp.a ⊓ centralizer (U : Set G) : Subgroup G))
    nlinarith
  have hh := SymmetricThreeTwoCore.normal_card_le_four_of_fixed_index_two e S V hc
    hVQ (U.subgroupOf P) hUS hUnot hfixindex
  rwa [Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv] at hh


/-- The normalized initial instance of the local cubic (9.2). -/
theorem normalized_nine_two
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (m : ctx.Γ.Vertex) (hm : m ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (hindex : QuotientCardEq (ZAt ctx.Γ ctx.criticalPath.a)
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ ZAt ctx.Γ m) 2)
    (hgenerate : QAt ctx.Γ m ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) = GAt ctx.Γ ctx.criticalPath.firstStep) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 :=
  Nat.le_antisymm (center_card_le_four_of_neighbor_index_two ctx.sectionSeven
    ctx.Γ ctx.criticalPath e ctx.commutator_eq m hm hindex hgenerate)
    (nine_three_initial_center_card_lower_bound ctx)

/-- The center-order conclusion of (9.2) from genuine cubic local data. -/
theorem nine_two
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (d l m : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a' d)
    (hl : l ∈ Neighborhood ctx.Γ d) (hm : m ∈ Neighborhood ctx.Γ d)
    (hindex : QuotientCardEq (ZAt ctx.Γ l) (ZAt ctx.Γ l ⊓ ZAt ctx.Γ m) 2)
    (hgenerate : QAt ctx.Γ m ⊔ (GAt ctx.Γ l ⊓ GAt ctx.Γ d) = GAt ctx.Γ d) :
    Nat.card (ZAt ctx.Γ l) = 4 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  obtain ⟨alignment, _, hstep⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨endpoint, hendpoint⟩ := hd
  let initial := alignment * endpoint
  have hinitial : Γ.act initial cp.firstStep = d := by
    change Γ.act (alignment * endpoint) cp.firstStep = d
    rw [Γ.act_mul, hstep]
    exact hendpoint
  have hneighbor : Γ.act initial cp.a ∈ neighborhood Γ d := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    rw [← hinitial]
    exact adjacent_act Γ initial (Γ.adjacent_symm cp.firstStep_adj)
  obtain ⟨correction, hcorrection⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    d hneighbor hl
  have hfix : Γ.act (correction : G) d = d := by
    exact (Set.ext_iff.mp (Γ.stabilizer_def d) (correction : G)).mp correction.property
  let actor := initial * (correction : G)
  have hleft : Γ.act actor cp.a = l := by
    change Γ.act (initial * (correction : G)) cp.a = l
    rw [Γ.act_mul]
    exact hcorrection
  have hright : Γ.act actor cp.firstStep = d := by
    change Γ.act (initial * (correction : G)) cp.firstStep = d
    rw [Γ.act_mul, hinitial, hfix]
  let neighbor := Γ.act actor⁻¹ m
  have hneighbor_act : Γ.act actor neighbor = m := by
    change Γ.act actor (Γ.act actor⁻¹ m) = m
    rw [← Γ.act_mul, inv_mul_cancel, Γ.act_one]
  have hnext : Γ.act actor⁻¹ d = cp.firstStep := by
    rw [← hright, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
  have hneighbor_mem : neighbor ∈ Neighborhood Γ cp.firstStep := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    rw [← hnext]
    exact adjacent_act Γ actor⁻¹ ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hm)
  let conjugation := MulAut.conj actor⁻¹
  have hZa : (ZAt Γ cp.a).map conjugation.toMonoidHom = ZAt Γ l := by
    rw [← z_act Γ actor, hleft]
  have hZm : (ZAt Γ neighbor).map conjugation.toMonoidHom = ZAt Γ m := by
    rw [← z_act Γ actor, hneighbor_act]
  have hQm : (QAt Γ neighbor).map conjugation.toMonoidHom = QAt Γ m := by
    rw [← SevenSix.q_act Γ actor, hneighbor_act]
  have hGa : (GAt Γ cp.a).map conjugation.toMonoidHom = GAt Γ l := by
    change conjugateBy (stabilizer Γ cp.a) actor⁻¹ = stabilizer Γ l
    rw [← stabilizer_act Γ actor, hleft]
  have hGnext : (GAt Γ cp.firstStep).map conjugation.toMonoidHom = GAt Γ d := by
    change conjugateBy (stabilizer Γ cp.firstStep) actor⁻¹ = stabilizer Γ d
    rw [← stabilizer_act Γ actor, hright]
  have hindex_local : QuotientCardEq (ZAt Γ cp.a) (ZAt Γ cp.a ⊓ ZAt Γ neighbor) 2 := by
    unfold QuotientCardEq at hindex ⊢
    rw [← hZa, ← hZm, ← Subgroup.map_inf _ _ _ conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective] at hindex
    exact hindex
  have hgenerate_local : QAt Γ neighbor ⊔ (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) =
      GAt Γ cp.firstStep := by
    apply (Subgroup.map_injective (f := conjugation.toMonoidHom) conjugation.injective)
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ conjugation.injective,
      hQm, hGa, hGnext]
    exact hgenerate
  have hcard := normalized_nine_two ctx e neighbor hneighbor_mem hindex_local hgenerate_local
  rw [← hZa, Subgroup.card_map_of_injective conjugation.injective]
  exact hcard

end Stellmacher.SectionNine.LocalCubic

namespace CFSG.Quasithin.ChapterF
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The literal Goldschmidt application discharges the cubic quotient premise in local (9.2). -/
theorem IsGoldschmidtTriple.critical_center_card_four_of_neighbor_index_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (d l m : Γ.Vertex) (hd : IsConjugateVertex Γ cp.a' d)
    (hl : l ∈ Neighborhood Γ d) (hm : m ∈ Neighborhood Γ d)
    (hindex : QuotientCardEq (ZAt Γ l) (ZAt Γ l ⊓ ZAt Γ m) 2)
    (hgenerate : QAt Γ m ⊔ (GAt Γ l ⊓ GAt Γ d) = GAt Γ d) :
    Nat.card (ZAt Γ l) = 4 := by
  let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
    ⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩
  have he : Nonempty (((stabilizer Γ cp.a) ⧸ pCore 2 (stabilizer Γ cp.a)) ≃*
      Equiv.Perm (Fin 3)) := by
    rcases cp.edge_stabilizers_are_P with he | he
    · rw [show stabilizer Γ cp.a = G₁ from he.1]
      exact h.quotient_left
    · rw [show stabilizer Γ cp.a = G₂ from he.1]
      exact h.quotient_right
  exact Stellmacher.SectionNine.LocalCubic.nine_two ctx he.some d l m hd hl hm hindex hgenerate

end CFSG.Quasithin.ChapterF
