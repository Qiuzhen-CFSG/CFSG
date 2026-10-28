module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Core
public import Theory.GroupAction.FaithfulSixteen

/-!
# The local action on the sixteen neighbors

The literal overlap H₁ ∩ H₂ acts faithfully on O₂(H₁). Its element of
order fifteen acts transitively on the fifteen nonidentity core elements.
Together with the actual complement decomposition this proves maximality
of the overlap and double transitivity on the neighbor orbit whenever the
edge stabilizer is that overlap. The graph theorem then supplies faithful
triple transitivity, degree seventeen and order 8160 from the edge identity
and the cubic word constructing a triangle.

Neither the edge identity nor the existence of that cubic word is assumed
in `SourceData`; they are the remaining source steps to prove. This module
does not assert the complete Baumeister source family.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.7, p.497.
-/

@[expose] public noncomputable section
open Subgroup MulAction
namespace Sporadic.Janko3.SourceRecognition.Seventeen

private theorem local_two_transitive {H X : Type*} [Group H] [MulAction H X]
    (V C : Subgroup H) [V.Normal] (hcomp : V.IsComplement' C) (b : X)
    (hstab : stabilizer H b = C)
    (htrans : ∀ x y : V, x ≠ 1 → y ≠ 1 →
      ∃ c : C, (c : H) * (x : H) * (c : H)⁻¹ = (y : H)) :
    ∀ x y u v : X, x ∈ orbit H b → y ∈ orbit H b → u ∈ orbit H b → v ∈ orbit H b →
      x ≠ y → u ≠ v → ∃ g : H, g • x = u ∧ g • y = v := by
  have hV (x : X) (hx : x ∈ orbit H b) : ∃ a : V, (a : H) • b = x := by
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨⟨a, c⟩, hac, _⟩ := hcomp.existsUnique g
    refine ⟨a, ?_⟩
    have hc : (c : H) • b = b := hstab ▸ c.property
    change (a : H) • b = g • b
    rw [← hac]
    change (a : H) • b = ((a : H) * c) • b
    rw [mul_smul, hc]
  intro x y u v hx hy hu hv hxy huv
  obtain ⟨a, rfl⟩ := hV x hx
  obtain ⟨d, rfl⟩ := hV y hy
  obtain ⟨e, rfl⟩ := hV u hu
  obtain ⟨f, rfl⟩ := hV v hv
  have had : a⁻¹ * d ≠ 1 := by
    intro hh
    exact hxy (congrArg (fun z : V => (z : H) • b) (inv_mul_eq_one.mp hh))
  have hef : e⁻¹ * f ≠ 1 := by
    intro hh
    exact huv (congrArg (fun z : V => (z : H) • b) (inv_mul_eq_one.mp hh))
  obtain ⟨c, hc⟩ := htrans (a⁻¹ * d) (e⁻¹ * f) had hef
  have hcb : (c : H) • b = b := hstab ▸ c.property
  refine ⟨(e : H) * c * (a : H)⁻¹, ?_, ?_⟩
  · simp only [mul_smul, inv_smul_smul, hcb]
  · have hw : (e : H) * c * (a : H)⁻¹ * d = (f : H) * c := by
      change (c : H) * ((a : H)⁻¹ * d) * (c : H)⁻¹ = (e : H)⁻¹ * f at hc
      calc
        (e : H) * c * (a : H)⁻¹ * d = e * (c * ((a : H)⁻¹ * d) * (c : H)⁻¹) * c := by group
        _ = (f : H) * c := by rw [hc]; group
    rw [← mul_smul, hw, mul_smul, hcb]

namespace SourceData
variable {G : Type*} [Group G] (S : SourceData G)

def overlapEquiv : S.H2.subgroupOf S.H1 ≃* Complement :=
  ((MulEquiv.subgroupCongr (inf_subgroupOf_left S.H2 S.H1).symm).trans
    (subgroupOfEquivOfLe inf_le_left)).trans S.overlap12

def overlapAction : S.H2.subgroupOf S.H1 →* MulAut (pCore 2 S.H1) :=
  (pCore 2 S.H1).normalizerMonoidHom.comp
    (inclusion (by rw [(pCore 2 S.H1).normalizer_eq_top]; exact le_top))

theorem overlapAction_injective : Function.Injective (overlapAction S) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hc : (x : S.H1) ∈ centralizer (pCore 2 S.H1 : Set S.H1) := by
    have hk : inclusion (show S.H2.subgroupOf S.H1 ≤
        normalizer (pCore 2 S.H1 : Set S.H1) from
        by rw [(pCore 2 S.H1).normalizer_eq_top]; exact le_top) x ∈
        (pCore 2 S.H1).normalizerMonoidHom.ker := hx
    rwa [normalizerMonoidHom_ker] at hk
  rw [S.core_centralizer] at hc
  exact Subtype.ext ((overlap_core_disjoint S).le_bot ⟨x.property, hc⟩)

theorem overlap_transitive_core_nonidentity (x y : pCore 2 S.H1) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ c : S.H2.subgroupOf S.H1, (c : S.H1) * (x : S.H1) * (c : S.H1)⁻¹ = (y : S.H1) := by
  let a : S.H2.subgroupOf S.H1 := (overlapEquiv S).symm
    (Multiplicative.ofAdd (1 : ZMod 3), DihedralGroup.r 1)
  have ha : orderOf a = 15 := by
    rw [← orderOf_injective (overlapEquiv S).toMonoidHom (overlapEquiv S).injective a]
    change orderOf ((overlapEquiv S) ((overlapEquiv S).symm _)) = 15
    rw [MulEquiv.apply_symm_apply]
    rw [Prod.orderOf_mk, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one, DihedralGroup.orderOf_r_one]
    decide
  have ho : orderOf (overlapAction S a) = 15 :=
    (orderOf_injective (overlapAction S) (overlapAction_injective S) a).trans ha
  let : Finite (pCore 2 S.H1) := Nat.finite_of_card_ne_zero (by rw [core_card S]; decide)
  obtain ⟨n, hn⟩ := MulAut.exists_zpow_apply_eq_of_order_fifteen
    (core_card S) (overlapAction S a) ho x y hx hy
  refine ⟨a ^ n, ?_⟩
  have he : overlapAction S (a ^ n) x = y := by simpa only [map_zpow] using hn
  exact congrArg Subtype.val he

theorem overlap_maximal : IsCoatom (S.H2.subgroupOf S.H1) := by
  let V := pCore 2 S.H1
  let C := S.H2.subgroupOf S.H1
  have hcomp : V.IsComplement' C := overlap_complements_core S
  have hn : V ≠ ⊥ := by
    intro hh
    have hc := core_card S
    change Nat.card V = 16 at hc
    rw [hh, Subgroup.card_bot] at hc
    norm_num at hc
  change IsCoatom C
  apply (SetLike.isCoatom_iff).mpr
  constructor
  · intro hc
    exact hn (by simpa only [hc, disjoint_top] using hcomp.disjoint)
  · intro K g hCK hgC hgK
    obtain ⟨⟨v, c⟩, hvc, _⟩ := hcomp.existsUnique g
    have hv : (v : S.H1) ∈ K := by
      have hc : (c : S.H1) ∈ K := hCK c.property
      have hm := K.mul_mem hgK (K.inv_mem hc)
      rw [← hvc] at hm
      simpa only [mul_inv_cancel_right] using hm
    have hv1 : v ≠ 1 := by
      intro he
      apply hgC
      rw [← hvc, he]
      change (1 : S.H1) * c ∈ C
      rw [one_mul]
      exact c.property
    have hVK : V ≤ K := by
      intro w hw
      by_cases hw1 : w = 1
      · simpa only [hw1] using K.one_mem
      · obtain ⟨d, hd⟩ := overlap_transitive_core_nonidentity S v ⟨w, hw⟩ hv1
          (fun hh => hw1 (congrArg Subtype.val hh))
        change (d : S.H1) * v * (d : S.H1)⁻¹ = w at hd
        rw [← hd]
        exact K.mul_mem (K.mul_mem (hCK d.property) hv) (K.inv_mem (hCK d.property))
    exact top_unique (hcomp.sup_eq_top ▸ sup_le hVK hCK)

theorem neighbor_two_transitive_of_edge
    (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1)
    (hedge : CosetGraph.edgeStabilizer (cosetData S b hb hbout) = S.H2.subgroupOf S.H1) :
    CosetGraph.NeighborTwoTransitive (cosetData S b hb hbout) := by
  let D := cosetData S b hb hbout
  have ht := local_two_transitive (pCore 2 S.H1) (S.H2.subgroupOf S.H1)
    (overlap_complements_core S) (CosetGraph.other D) hedge
    (overlap_transitive_core_nonidentity S)
  intro x y u v hx hy hu hv hxy huv
  have horbit (x : CosetGraph.Vertex D)
      (hx : (CosetGraph.graph D).Adj (CosetGraph.base D) x) :
      x ∈ orbit S.H1 (CosetGraph.other D) := by
    rw [CosetGraph.graph, SwappedOrbital.adj_base, CosetGraph.point_stabilizer] at hx
    exact hx
  obtain ⟨g, hgx, hgy⟩ := ht x y u v (horbit x hx) (horbit y hy) (horbit u hu) (horbit v hv) hxy huv
  refine ⟨⟨g, ?_⟩, hgx, hgy⟩
  rw [CosetGraph.point_stabilizer]
  exact g.property

theorem geometric_consequences_of_edge_cube
    (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2)
    (hedge : CosetGraph.edgeStabilizer (cosetData S b hb hbout) = S.H2.subgroupOf S.H1)
    (h : G) (hh : h ∈ S.H1) (hcube : (b * h)^3 ∈ S.H1) :
    let D := cosetData S b hb hbout
    FaithfulSMul G (CosetGraph.Vertex D) ∧
      (CosetGraph.graph D).Connected ∧ CosetGraph.graph D = ⊤ ∧
      (∀ x : CosetGraph.Vertex D, Nat.card ((CosetGraph.graph D).neighborSet x) = 16) ∧
      Nat.card (CosetGraph.Vertex D) = 17 ∧
      IsMultiplyPretransitive G (CosetGraph.Vertex D) 3 ∧ Nat.card G = 8160 :=
  ⟨faithful_of_edge S b hb hbout hedge,
    geometric_consequences S b hb hbout hb2 hedge
      (neighbor_two_transitive_of_edge S b hb hbout hedge) h hh hcube⟩

end SourceData
end Sporadic.Janko3.SourceRecognition.Seventeen
