module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5Local
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Finite-order ordinary rows in the original A₅ configuration

A nonnormal A₅ component has a span of five-rank at least two. The
ordinary placement preserves this rank through the central quotient.
The five Mathieu groups, J₄, binary PSL₄ and PSL₅, and the small derived
G₂ group have no factor 25 in their orders. The small derived symplectic
group is the literal alternating-six carrier. Thus each row forces the
original component to be normalized.

Source: Aschbacher–Smith C.3.1 and C.4.8, printed pp.149–154, specialized
to the original A₅ covering configuration of 4.2.12–13, pp.610–611.
-/

public section
open Subgroup Theory.GroupTheory


namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

theorem normalizes_a5_of_ordinary_quotient_order
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (ho : ¬ 25 ∣ Nat.card (K ⧸ center K)) : M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact h.normalizes_a5_of_ordinary_quotient_fiveRank_le_one a K hK
    (primeRank_le_one_of_square_not_dvd ho)

theorem normalizes_a5_of_ordinary_small_sporadic
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (n : ClassificationModels.SporadicName)
    (hn : n = .m11 ∨ n = .m12 ∨ n = .m22 ∨ n = .m23 ∨ n = .m24 ∨ n = .j4)
    (e : K ⧸ center K ≃* n.Carrier) : M ≤ normalizer (L : Set G) := by
  apply h.normalizes_a5_of_ordinary_quotient_order a K hK
  rw [Nat.card_congr e.toEquiv]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · change ¬25 ∣ Nat.card Sporadic.Mathieu.M11
    rw [Sporadic.Mathieu.m11_order]; decide
  · change ¬25 ∣ Nat.card Sporadic.Mathieu.M12
    rw [Sporadic.Mathieu.m12_order]; decide
  · change ¬25 ∣ Nat.card Sporadic.Mathieu.M22
    rw [Sporadic.Mathieu.m22_order]; decide
  · change ¬25 ∣ Nat.card Sporadic.Mathieu.M23
    rw [Sporadic.Mathieu.m23_order]; decide
  · change ¬25 ∣ Nat.card Sporadic.Mathieu.M24
    rw [Sporadic.Mathieu.m24_order]; decide
  · change ¬25 ∣ Nat.card Janko4.Model
    rw [Janko4.Cardinality.model_card]; decide

theorem normalizes_a5_of_ordinary_g2_derived_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_a5_of_ordinary_quotient_order a K hK
  rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
  decide

theorem normalizes_a5_of_ordinary_linear_binary
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) n 2) : M ≤ normalizer (L : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  apply h.normalizes_a5_of_ordinary_quotient_order a K hK
  rw [Nat.card_congr e.toEquiv]
  rcases hn with rfl | rfl
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [hc]; decide
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [hc]; decide

theorem normalizes_a5_of_ordinary_sp_derived_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) :
    M ≤ normalizer (L : Set G) :=
  h.normalizes_a5_of_ordinary_alternating a K hK (by decide : 6 ≤ 8)
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
end CFSG.Quasithin.ChapterC.HypothesisC28
