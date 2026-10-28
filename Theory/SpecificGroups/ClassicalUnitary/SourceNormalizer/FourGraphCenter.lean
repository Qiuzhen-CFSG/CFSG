module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraphSylow
public import Theory.Frattini.OmegaProducts
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CommutatorRows
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Frattini

/-!
# The characteristic root plane in the unitary graph-fixed Sylow

For q>2 the derived group of the symplectic unipotent group is its
central two-root plane. The coordinate square is a commutator; the proved
Frattini calculation therefore gives the reverse inclusion to class two.
In the full graph-fixed Sylow U×C₂ the center–derived intersection is
exactly Z(U)×1, of order q² and elementary abelian. The graph factor is
retained, and is disjoint from that characteristic plane.

Source: Aschbacher–Smith F.4.37(4), printed p.293 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
open SymplecticFour SymplecticFour.CentralRootGeometry UnitaryFourOuter
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
private theorem square_commutator (b u w v : K) :
    (element b u w v)^2 = ⁅element b 0 0 0,element 0 0 0 v⁆ := by
  rw [element_square,commutatorElement_def]
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply (eq_mul_inv_iff_mul_eq).mpr
  simp only [theta,element_mul]
  apply (element_eq_iff _ _ _ _ _ _ _ _).mpr
  simp [CharTwo.add_self_eq_zero,mul_comm,mul_left_comm,pow_two]

/-- At every nonbinary parameter, including q=4, the fixed unipotent
derived group is its full central two-root plane. -/
theorem fixed_unipotent_derived {m : ℕ} (hK : Nat.card K = 2^m) (hm : 1 < m) :
    _root_.commutator (unipotent (F := K)) = center (unipotent (F := K)) := by
  apply le_antisymm class_two
  rw [←frattini_eq_center hK hm,(isPGroup_unipotent hK).frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro _ ⟨x,rfl⟩
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  change (element b u w v)^2 ∈ _
  rw [square_commutator]
  exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)

/-- Exact characteristic plane in the graph-fixed Sylow, with the original
central graph factor still present in the ambient direct product. -/
theorem fixed_product_center_derived {m : ℕ} (hK : Nat.card K = 2^m) (hm : 1 < m) :
    center ((unipotent (F := K)) × C2) ⊓
        _root_.commutator ((unipotent (F := K)) × C2) =
      (center (unipotent (F := K))).prod (⊥ : Subgroup C2) := by
  have hd : _root_.commutator ((unipotent (F := K)) × C2) =
      (center (unipotent (F := K))).prod (⊥ : Subgroup C2) := by
    change ⁅(⊤ : Subgroup ((unipotent (F := K)) × C2)),⊤⁆ = _
    rw [←top_prod_top,commutator_prod_prod]
    change (_root_.commutator (unipotent (F := K))).prod (_root_.commutator C2) = _
    rw [fixed_unipotent_derived hK hm,commutator_eq_bot]
  rw [hd,Subgroup.center_prod]
  exact inf_eq_right.mpr (prod_mono le_rfl bot_le)

/-- The two independent root coordinates give the exact order q². -/
theorem fixed_product_center_derived_card {m : ℕ}
    (hK : Nat.card K = 2^m) (hm : 1 < m) :
    Nat.card (center ((unipotent (F := K)) × C2) ⊓
      _root_.commutator ((unipotent (F := K)) × C2) : Subgroup _) = (2^m)^2 := by
  rw [fixed_product_center_derived hK hm,
    Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,card_bot,mul_one,
    ←Nat.card_congr (centerEquiv (F := K)).toEquiv,Nat.card_prod]
  simp only [Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K),hK,pow_two]

/-- Every element of this characteristic plane has square one. -/
theorem fixed_product_center_derived_square {m : ℕ}
    (hK : Nat.card K = 2^m) (hm : 1 < m)
    (x : (unipotent (F := K)) × C2)
    (hx : x ∈ center ((unipotent (F := K)) × C2) ⊓
      _root_.commutator ((unipotent (F := K)) × C2)) : x^2 = 1 := by
  rw [fixed_product_center_derived hK hm] at hx
  let : IsElementaryAbelian 2 (center (unipotent (F := K))) := center_elementary
  apply Prod.ext
  · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) x.1 hx.1
  · change x.2^2=1
    rw [show x.2=1 from hx.2,one_pow]

private def productSylow {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) : Sylow 2 (X × C2) := by
  have hc : Nat.card C2=2 := by
    rw [Nat.card_congr (Multiplicative.toAdd : C2 ≃ ZMod 2),
      Nat.card_eq_fintype_card,ZMod.card]
  have hp : IsPGroup 2 (P × (⊤ : Subgroup C2)) := by
    obtain ⟨a,ha⟩ := P.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a+1)
    rw [Nat.card_prod,ha,card_top,hc,pow_succ]
  exact (hp.of_equiv (prodEquiv (P : Subgroup X) ⊤).symm).toSylow (by
    rw [index_prod,index_top,mul_one]
    exact P.not_dvd_index)

/-- Every Sylow of a graph-fixed overgroup of the unipotent group has the same actual product
structure. This is constructed by Sylow conjugacy within that overgroup. -/
def fixed_overgroup_sylow_equiv {m : ℕ} (hK : Nat.card K=2^m) (hm : 1≤m)
    (D : Subgroup (Sp K)) (hD : unipotent ≤ D)
    (P : Sylow 2 (D × C2)) :
    P ≃* ((unipotent (F := K)) × C2) :=
  (P.equiv (productSylow ((unipotentSylow hK hm).subtype hD))).trans
    ((prodEquiv _ _).trans
      (MulEquiv.prodCongr (subgroupOfEquivOfLe hD) (topEquiv)))

/-- The center–derived intersection is transported as one characteristic
subgroup under the specified isomorphism. -/
@[expose] def centerDerivedEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (center X ⊓ _root_.commutator X : Subgroup X) ≃*
      (center Y ⊓ _root_.commutator Y : Subgroup Y) :=
  ((center X ⊓ _root_.commutator X : Subgroup X).equivMapOfInjective
    e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr (by
      rw [map_inf _ _ _ e.injective,center_map_equiv,map_commutator_eq,
        MonoidHom.range_eq_top.mpr e.surjective]
      rfl))

/-- The characteristic plane of every full graph-fixed local Sylow has
order q², including at the smallest allowed parameter q=4. -/
theorem fixed_overgroup_sylow_center_derived_card {m : ℕ}
    (hK : Nat.card K=2^m) (hm : 1<m)
    (D : Subgroup (Sp K)) (hD : unipotent ≤ D)
    (P : Sylow 2 (D × C2)) :
    Nat.card (center P ⊓ _root_.commutator P : Subgroup P) = (2^m)^2 := by
  rw [Nat.card_congr (centerDerivedEquiv (fixed_overgroup_sylow_equiv hK hm.le D hD P)).toEquiv]
  exact fixed_product_center_derived_card hK hm

theorem fixed_overgroup_sylow_center_derived_square {m : ℕ}
    (hK : Nat.card K=2^m) (hm : 1<m)
    (D : Subgroup (Sp K)) (hD : unipotent ≤ D)
    (P : Sylow 2 (D × C2))
    (x : P) (hx : x ∈ center P ⊓ _root_.commutator P) : x^2=1 := by
  let e := fixed_overgroup_sylow_equiv hK hm.le D hD P
  have hh := fixed_product_center_derived_square hK hm
    (e x) (centerDerivedEquiv e ⟨x,hx⟩).property
  apply e.injective
  simpa only [map_pow,map_one] using hh

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
