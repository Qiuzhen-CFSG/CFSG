module
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A self-paired orbital graph

An element exchanging a pair of distinct points makes its orbital symmetric.
The original action preserves the resulting simple graph. If the base
stabilizer has just the base point, this neighbor orbit, and its complement,
then the graph is strongly regular. All transport uses the given action.

Source: the rank-three graph argument preceding Aschbacher–Smith J.5.5.
-/

@[expose] public section
noncomputable section
namespace MulAction.SwappedOrbital
open MulAction
variable {G Ω:Type*} [Group G] [MulAction G Ω]
variable (a b:Ω) (hab:a≠b) (t:G) (hta:t•a=b) (htb:t•b=a)

def graph : SimpleGraph Ω where
  Adj x y := ∃g:G,g•a=x ∧ g•b=y
  symm := ⟨by
    rintro x y ⟨g,rfl,rfl⟩
    exact ⟨g*t,by rw [mul_smul,hta],by rw [mul_smul,htb]⟩⟩
  loopless := ⟨by
    rintro x ⟨g,hx,hy⟩
    exact hab ((MulAction.injective g) (hx.trans hy.symm))⟩

theorem adj_smul_iff (g:G) (x y:Ω) :
    (graph a b hab t hta htb).Adj (g•x) (g•y) ↔ (graph a b hab t hta htb).Adj x y := by
  constructor
  · rintro ⟨h,hx,hy⟩
    refine ⟨g⁻¹*h,?_,?_⟩
    · rw [mul_smul,hx,inv_smul_smul]
    · rw [mul_smul,hy,inv_smul_smul]
  · rintro ⟨h,rfl,rfl⟩
    exact ⟨g*h,mul_smul _ _ _,mul_smul _ _ _⟩

theorem adj_base (x:Ω) :
    (graph a b hab t hta htb).Adj a x ↔ x∈orbit (stabilizer G a) b := by
  constructor
  · rintro ⟨g,hg,hx⟩; exact ⟨⟨g,hg⟩,hx⟩
  · rintro ⟨g,hg⟩; exact ⟨g,g.property,hg⟩

theorem neighbor_base : (graph a b hab t hta htb).neighborSet a=orbit (stabilizer G a) b :=
  Set.ext (adj_base a b hab t hta htb)

def automorphism (g:G) : graph a b hab t hta htb ≃g graph a b hab t hta htb where
  toEquiv:=MulAction.toPerm g
  map_rel_iff':=adj_smul_iff a b hab t hta htb g _ _

def neighborsEquiv (g:G) (x:Ω) :
    (graph a b hab t hta htb).neighborSet x ≃
      (graph a b hab t hta htb).neighborSet (g•x) where
  toFun y:=⟨g•y,(adj_smul_iff a b hab t hta htb g x y).mpr y.property⟩
  invFun y:=⟨g⁻¹•y,by
    have h:=(adj_smul_iff a b hab t hta htb g⁻¹ (g•x) y).mpr y.property
    change (graph a b hab t hta htb).Adj x (g⁻¹•y)
    simpa only [inv_smul_smul] using h⟩
  left_inv _:=Subtype.ext (inv_smul_smul _ _)
  right_inv _:=Subtype.ext (smul_inv_smul _ _)

def commonNeighborsEquiv (g:G) (x y:Ω) :
    (graph a b hab t hta htb).commonNeighbors x y ≃
      (graph a b hab t hta htb).commonNeighbors (g•x) (g•y) where
  toFun z:=⟨g•z,⟨(adj_smul_iff a b hab t hta htb g x z).mpr z.property.1,
    (adj_smul_iff a b hab t hta htb g y z).mpr z.property.2⟩⟩
  invFun z:=⟨g⁻¹•z,by
    have hx:=(adj_smul_iff a b hab t hta htb g⁻¹ (g•x) z).mpr z.property.1
    have hy:=(adj_smul_iff a b hab t hta htb g⁻¹ (g•y) z).mpr z.property.2
    change (graph a b hab t hta htb).Adj x (g⁻¹•z) ∧
      (graph a b hab t hta htb).Adj y (g⁻¹•z)
    simpa only [inv_smul_smul] using And.intro hx hy⟩
  left_inv _:=Subtype.ext (inv_smul_smul _ _)
  right_inv _:=Subtype.ext (smul_inv_smul _ _)

attribute [local instance] Classical.propDecidable

theorem stronglyRegular [Fintype Ω] [IsPretransitive G Ω] (c:Ω)
    (hc:orbit (stabilizer G a) c=(({a}:Set Ω)∪orbit (stabilizer G a) b)ᶜ) :
    (graph a b hab t hta htb).IsSRGWith (Nat.card Ω)
      (Nat.card (orbit (stabilizer G a) b))
      (Nat.card ((graph a b hab t hta htb).commonNeighbors a b))
      (Nat.card ((graph a b hab t hta htb).commonNeighbors a c)) := by
  let Γ:=graph a b hab t hta htb
  constructor
  · exact Nat.card_eq_fintype_card.symm
  · intro x
    obtain ⟨g,rfl⟩:=exists_smul_eq G a x
    rw [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      ← Nat.card_congr (neighborsEquiv a b hab t hta htb g a),neighbor_base]
  · rintro x y ⟨g,rfl,rfl⟩
    rw [← Nat.card_eq_fintype_card,
      ← Nat.card_congr (commonNeighborsEquiv a b hab t hta htb g a b)]
  · intro x y hxy hnon
    obtain ⟨g,rfl⟩:=exists_smul_eq G a x
    have hz:g⁻¹•y∈orbit (stabilizer G a) c:=by
      rw [hc]
      rintro (he|he)
      · exact hxy (by rw [Set.mem_singleton_iff] at he; rw [←he,smul_inv_smul])
      · have ha':= (adj_base a b hab t hta htb _).mpr he
        have hh:=(adj_smul_iff a b hab t hta htb g a (g⁻¹•y)).mpr ha'
        exact hnon (by simpa only [smul_inv_smul] using hh)
    obtain ⟨k,hk⟩:=hz
    change (k:G)•c=g⁻¹•y at hk
    have hx:(g*(k:G))•a=g•a:=by rw [mul_smul,k.property]
    have hy:(g*(k:G))•c=y:=by rw [mul_smul,hk,smul_inv_smul]
    rw [←hx,←hy,← Nat.card_eq_fintype_card,
      ← Nat.card_congr (commonNeighborsEquiv a b hab t hta htb (g*(k:G)) a c)]

end MulAction.SwappedOrbital
