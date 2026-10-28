module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PairDihedral
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.OddCore
public import Theory.GroupTheory.InvertedOddPairOrders

/-!
# Original inverted odd orders and the remaining five-core

Lift an odd-order element of H/O₂(H) to the original H. If an element
of V-star inverts it, the two conjugates of V supply a pair image
containing its inverse square. That image cannot be a two-group, so the
proved original dihedral alternatives force order three or five.
All maps here are the literal quotient projection and ambient conjugation;
the chosen lift is the same conjugating element used in the pair theorem.

For a normal p-subgroup moved by an involution, a nonidentity commutator
is inverted by that involution. The order restriction therefore proves
centralization of every p-core for p different from two, three and five.
Together with the existing three-core exclusion, this discharges every
odd-core premise of original component selection except the five-core.

The five-core exclusion, subsequent component analysis, abelianness of
the point span and universal NaturalReduction remain unproved. Earlier
point, fixed-space, intersection and nonsingular-centralizer inputs remain
explicit and are not inferred from a guard on the original group.
Source: Aschbacher--Smith, proof of 12.6.26, printed pp.831--832.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Nonidentity odd-order elements inverted by the original V-star have order three or five. -/
theorem SourceHypothesis.original_star_inverted_odd_order
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (t : H ⧸ pCore 2 H) (ht : t ∈ Nonabelian.Setup.star H V)
    (x : H ⧸ pCore 2 H) (hx : x ≠ 1) (ho : Odd (orderOf x))
    (hi : t*x*t⁻¹=x⁻¹) : orderOf x=3 ∨ orderOf x=5 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  obtain ⟨v,hv,rfl⟩ := ht
  let I := V ⊔ V.map (MulAut.conj g.val).toMonoidHom
  let B := Nonabelian.Setup.star H I
  have ht2 : (q v)^2=1 := by
    rw [←map_pow,show v^2=1 from Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val hv),map_one]
  have htB : q v ∈ B := mem_map_of_mem q (mem_sup_left hv)
  have hcB : q g * q v * (q g)⁻¹ ∈ B := by
    have hm : g*v*g⁻¹ ∈ I.subgroupOf H :=
      mem_sup_right (mem_map_of_mem (MulAut.conj g.val).toMonoidHom hv)
    simpa only [map_mul,map_inv,B,Nonabelian.Setup.star] using mem_map_of_mem q hm
  apply inverted_odd_order_of_pair_card B (q v) (q g) ht2 htB hcB hi ho hx
  intro hn
  have hnI : ¬ IsPGroup 2 I := fun hp =>
    hn ((hp.comap_of_injective H.subtype H.subtype_injective).map q)
  obtain ⟨_,_,m,_,hm,⟨e⟩,_⟩ :=
    S.original_non_two_pair_dihedral D hZ z hz hTV hTz hbound hns hH g.val g.property hnI
  have hc : Nat.card B=2*m := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  rcases hm with rfl|rfl|rfl
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hc)

/-- Every prime core other than the two-, three-, and five-cores is centralized by V-star. -/
theorem SourceHypothesis.original_star_other_odd_core_centralized
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    Nonabelian.Setup.star H V ≤ centralizer (pCore p (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) := by
  let : Fact p.Prime := ⟨hp⟩
  intro t ht
  have ht2 : t^2=1 := by
    obtain ⟨v,hv,rfl⟩ := ht
    rw [←map_pow,show v^2=1 from Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val hv),map_one]
  exact centralizes_pGroup_of_inverted_orders t ht2
    (S.original_star_inverted_odd_order D hZ z hz hTV hTz hbound hns hH t ht)
    hp2 hp3 hp5 (pCore p _) pCore_isPGroup

/-- Component selection now requires only the five-core exclusion, besides earlier geometry. -/
theorem SourceHypothesis.original_selectedComponent_of_five_core
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (hfive : Nonabelian.Setup.star H V ≤
      centralizer (pCore 5 (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H))) :
    Nonempty ((D.fullSetup hZ T z).SelectedComponent H) := by
  apply S.original_selectedComponent_of_large_odd_cores D hZ z hz hTV hTz hbound hH hn
  intro p hp hgt
  by_cases h5 : p=5
  · exact h5 ▸ hfive
  exact S.original_star_other_odd_core_centralized D hZ z hz hTV hTz hbound hns hH hp
    (by omega) (by omega) h5
end CFSG.Quasithin.Chapter12.Section06
