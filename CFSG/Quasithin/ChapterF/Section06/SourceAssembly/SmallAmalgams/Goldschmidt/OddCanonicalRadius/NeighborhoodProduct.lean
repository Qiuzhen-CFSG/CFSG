module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelFacts
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card

/-!
# The three-branch product and its local centralizer

The canonical neighbor-product relation says that changing a chosen label
in one branch multiplies it by the label at the center. The three branch
labels commute, so every conjugate of their product by the center stabilizer
is either that product or its product with the central label. Orbit-stabilizer
therefore bounds the local centralizer index by two.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.8) and
(6.11.2), printed pp.399--402.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem mul_mod_involution {z a b a' b' : G}
    (hz : z*z=1) (hzb : Commute z b)
    (ha : a'=a ∨ a'=a*z) (hb : b'=b ∨ b'=b*z) :
    a'*b'=a*b ∨ a'*b'=a*b*z := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact .inl rfl
  · exact .inr (mul_assoc _ _ _).symm
  · exact .inr (by rw [mul_assoc, hzb.eq, ← mul_assoc])
  · exact .inl (by rw [mul_assoc, hzb.left_comm, hz, mul_one])

private theorem triple_mod_involution (z : G) (x y : Fin 3 → G)
    (σ : Equiv.Perm (Fin 3)) (hz : z*z=1)
    (hcomm : ∀ i j, Commute (x i) (x j)) (hzc : ∀ i, Commute z (x i))
    (hy : ∀ i, y i=x (σ i) ∨ y i=x (σ i)*z) :
    y 0*y 1*y 2=x 0*x 1*x 2 ∨ y 0*y 1*y 2=x 0*x 1*x 2*z := by
  have hp := (σ.ofFn_comp_perm x).prod_eq'
    (List.pairwise_ofFn.mpr (fun _ _ _ => hcomm _ _))
  have he : x (σ 0)*x (σ 1)*x (σ 2)=x 0*x 1*x 2 := by
    simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      mul_one, mul_assoc] using hp
  have h01 := mul_mod_involution hz (hzc (σ 1)) (hy 0) (hy 1)
  have h012 := mul_mod_involution hz (hzc (σ 2)) h01 (hy 2)
  simpa only [he] using h012

private theorem centralizer_index_le_two_of_conjugates [Finite G] (v w : G)
    (hconj : ∀ g:G, g*v*g⁻¹=v ∨ g*v*g⁻¹=w) :
    (centralizer ({v}:Set G)).index  ≤  2 := by
  have hsub : MulAction.orbit (ConjAct G) v ⊆ ({v,w}:Set G) := by
    rintro a ⟨g,rfl⟩
    exact hconj (ConjAct.ofConjAct g)
  have hc : Nat.card (MulAction.orbit (ConjAct G) v)  ≤  2 := by
    exact (Set.ncard_le_ncard hsub).trans (by
      calc
        ({v,w}:Set G).ncard  ≤  ({w}:Set G).ncard+1 := Set.ncard_insert_le _ _
        _ = 2 := by simp)
  rw [Subgroup.centralizer_eq_comap_stabilizer]
  calc
    _ = (MulAction.stabilizer (ConjAct G) v).index :=
      Subgroup.index_comap_of_surjective _ (f := ConjAct.toConjAct.toMonoidHom)
        ConjAct.toConjAct.surjective
    _ = Nat.card (MulAction.orbit (ConjAct G) v) := MulAction.index_stabilizer _ _
    _  ≤  2 := hc

private theorem type_of_two_steps {a b c : RankTwo.Vertex F}
    (hab : (RankTwo.graph F).Adj a b) (hbc : (RankTwo.graph F).Adj b c) : c.type=a.type := by
  have h0 := hab.1
  have h1 := hbc.1
  cases h2 : a.type <;> cases h3 : b.type <;> cases h4 : c.type <;> simp_all

/-- At a branch vertex, the two labels away from the center differ by the
central label. This is the literal three-neighbor relation of (6.8). -/
theorem CanonicalLabelSetup.branch_label_alternative (d : CanonicalLabelSetup F s)
    {a b u w : RankTwo.Vertex F} (ha : a.type=d.side)
    (hab : (RankTwo.graph F).Adj a b) (hbu : (RankTwo.graph F).Adj b u)
    (hbw : (RankTwo.graph F).Adj b w) (hua : u≠a) (hwa : w≠a) :
    d.label w=d.label u ∨ d.label w=d.label u*d.label a := by
  by_cases he : w=u
  · exact .inl (congrArg d.label he)
  · have hu : u.type=d.side := (type_of_two_steps hab hbu).trans ha
    have hp := d.neighbor_product b u w a hbu hbw hab.symm (fun h => he h.symm) hua hwa hu
    have hp' : d.label u*d.label w=d.label a := by
      calc
        d.label u*d.label w = (d.label a)⁻¹ := mul_eq_one_iff_eq_inv.mp hp
        _ = d.label a := d.label_inv ha
    right
    calc
      d.label w = 1*d.label w := (one_mul _).symm
      _ = (d.label u*d.label u)*d.label w := by rw [d.label_mul_self hu]
      _ = d.label u*(d.label u*d.label w) := mul_assoc _ _ _
      _ = d.label u*d.label a := congrArg (d.label u*·) hp'

/-- A product selecting one label from each of the three branches has at most
two conjugates under the center stabilizer. -/
theorem CanonicalLabelSetup.threeBranchProduct_conjugates (d : CanonicalLabelSetup F s)
    (hr : 3 ≤ d.radius) (hs : 4 ≤ s) {a : RankTwo.Vertex F} (ha : a.type=d.side)
    (e : Fin 3 ≃ (RankTwo.graph F).neighborSet a) (u : Fin 3 → RankTwo.Vertex F)
    (hu : ∀ i, (RankTwo.graph F).Adj (e i).val (u i)) (hua : ∀ i, u i≠a)
    (g : G) (hg : g • a=a) :
    g*(d.label (u 0)*d.label (u 1)*d.label (u 2))*g⁻¹ =
        d.label (u 0)*d.label (u 1)*d.label (u 2) ∨
    g*(d.label (u 0)*d.label (u 1)*d.label (u 2))*g⁻¹ =
        d.label (u 0)*d.label (u 1)*d.label (u 2)*d.label a := by
  have hg' : g⁻¹ • a=a := by
    calc
      g⁻¹ • a = g⁻¹ • (g • a) := congrArg (g⁻¹ • ·) hg.symm
      _ = a := inv_smul_smul g a
  let f : Equiv.Perm ((RankTwo.graph F).neighborSet a) := {
    toFun b := ⟨g • b.val, by
      change (RankTwo.graph F).Adj a (g • b.val)
      simpa only [hg] using trackGraphAction.map_adj g b.property⟩
    invFun b := ⟨g⁻¹ • b.val, by
      change (RankTwo.graph F).Adj a (g⁻¹ • b.val)
      simpa only [hg'] using trackGraphAction.map_adj g⁻¹ b.property⟩
    left_inv b := Subtype.ext (inv_smul_smul g b.val)
    right_inv b := Subtype.ext (smul_inv_smul g b.val) }
  let σ : Equiv.Perm (Fin 3) := e.trans (f.trans e.symm)
  have hσ (i : Fin 3) : (e (σ i)).val=g • (e i).val :=
    congrArg Subtype.val (e.apply_symm_apply (f (e i)))
  have ht (i : Fin 3) : (u i).type=d.side :=
    (type_of_two_steps (e i).property (hu i)).trans ha
  have htwo (i : Fin 3) : (RankTwo.graph F).dist (u i) a ≤ 2 :=
    SimpleGraph.dist_le (.cons (hu i).symm (.cons (e i).property.symm .nil))
  have hc (i j : Fin 3) : Commute (d.label (u i)) (d.label (u j)) := by
    have hd : (RankTwo.graph F).dist (u i) (u j) ≤ 4 :=
      SimpleGraph.dist_le (.cons (hu i).symm (.cons (e i).property.symm
        (.cons (e j).property (.cons (hu j) .nil))))
    exact d.labels_commute_of_dist_le (ht i) (ht j) (by omega) (by omega)
  have hzc (i : Fin 3) : Commute (d.label a) (d.label (u i)) :=
    (d.central a ha).2 _ (d.fixes_ball (u i) (ht i) a (by have := htwo i; omega)
      (by have := htwo i; omega))
  have hy (i : Fin 3) : d.label (g • u i)=d.label (u (σ i)) ∨
      d.label (g • u i)=d.label (u (σ i))*d.label a := by
    apply d.branch_label_alternative ha (e (σ i)).property (hu (σ i))
    · rw [hσ]
      exact trackGraphAction.map_adj g (hu i)
    · exact hua (σ i)
    · intro he
      exact hua i ((MulAction.toPerm g).injective (he.trans hg.symm))
  have hp := triple_mod_involution (d.label a) (fun i => d.label (u i))
    (fun i => d.label (g • u i)) σ (d.label_mul_self ha) hc hzc hy
  have hconj (i : Fin 3) : d.label (g • u i)=(MulAut.conj g) (d.label (u i)) :=
    d.conjugate g (u i) (ht i)
  rw [hconj 0,hconj 1,hconj 2,← map_mul,← map_mul] at hp
  exact hp

/-- The orbit calculation is the source centralizer index bound (6.11.2). -/
theorem CanonicalLabelSetup.threeBranchProduct_centralizer_index_le_two
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    (hr : 3 ≤ d.radius) (hs : 4 ≤ s) {a : RankTwo.Vertex F} (ha : a.type=d.side)
    (e : Fin 3 ≃ (RankTwo.graph F).neighborSet a) (u : Fin 3 → RankTwo.Vertex F)
    (hu : ∀ i, (RankTwo.graph F).Adj (e i).val (u i)) (hua : ∀ i, u i≠a) :
    (centralizer ({d.label (u 0)*d.label (u 1)*d.label (u 2)}:Set G)).relIndex
      (RankTwo.stabilizer F a)  ≤  2 := by
  let H := RankTwo.stabilizer F a
  let : Finite H := h.finite_stabilizer a
  have hm (i : Fin 3) : d.label (u i)∈H := by
    have ht := (type_of_two_steps (e i).property (hu i)).trans ha
    have hd : (RankTwo.graph F).dist (u i) a ≤ 2 :=
      SimpleGraph.dist_le (.cons (hu i).symm (.cons (e i).property.symm .nil))
    exact d.fixes_ball (u i) ht a (by omega) (by omega)
  let v : H := ⟨d.label (u 0)*d.label (u 1)*d.label (u 2),
    H.mul_mem (H.mul_mem (hm 0) (hm 1)) (hm 2)⟩
  let z : H := ⟨d.label a, (d.central a ha).1⟩
  have hi := centralizer_index_le_two_of_conjugates v (v*z) (fun g => by
    rcases d.threeBranchProduct_conjugates hr hs ha e u hu hua g g.property with hg | hg
    · exact .inl (Subtype.ext hg)
    · exact .inr (Subtype.ext hg))
  have he : centralizer ({v}:Set H)=
      (centralizer ({v.val}:Set G)).subgroupOf H := by
    ext x
    simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subtype.ext_iff, coe_mul]
  rwa [he] at hi

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
