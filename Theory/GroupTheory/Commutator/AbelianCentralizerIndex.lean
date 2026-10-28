module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic

/-!
# Centralizer indices from an abelian commutator map

When [V,Q] lies in an abelian subgroup Z of V, the map v ↦ [v,t]
for t in Q is a homomorphism V → Z. Its kernel is C_V(t), so its
index is at most |Z|. If C_V(t) lies in a prescribed intersection of
that index, the two subgroups coincide.

The source application is the trapped-centralizer branch of DGS85
(12.7), Groups and Graphs (1985), printed p.184.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem abelian_singleton_centralizer_index_le
    (V Q Z : Subgroup G) [Finite Z] [IsMulCommutative V]
    (hZ : Z ≤ V) (hcomm : ⁅V,Q⁆ ≤ Z) {t : G} (ht : t ∈ Q) :
    (centralizer ({t} : Set G)).relIndex V ≤ Nat.card Z := by
  let f : V →* Z := {
    toFun v := ⟨⁅(v : G),t⁆, hcomm (commutator_mem_commutator v.property ht)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' v w := by
      apply Subtype.ext
      change ⁅(v : G)*(w : G),t⁆ = ⁅(v : G),t⁆ * ⁅(w : G),t⁆
      have hw := hZ (hcomm (commutator_mem_commutator w.property ht))
      have hv := hZ (hcomm (commutator_mem_commutator v.property ht))
      have hc : (v : G) * ⁅(w : G),t⁆ = ⁅(w : G),t⁆ * v :=
        congrArg Subtype.val (mul_comm v (⟨_,hw⟩ : V))
      have hd : ⁅(w : G),t⁆ * ⁅(v : G),t⁆ = ⁅(v : G),t⁆ * ⁅(w : G),t⁆ :=
        congrArg Subtype.val (mul_comm (⟨_,hw⟩ : V) ⟨_,hv⟩)
      rw [commutatorElement_mul_left_eq_conj_mul,hc,mul_inv_cancel_right,hd] }
  have hk : f.ker = (centralizer ({t} : Set G)).subgroupOf V := by
    ext v
    change (⟨⁅(v : G),t⁆,_⟩ : Z) = 1 ↔ _
    rw [Subtype.ext_iff]
    change ⁅(v : G),t⁆ = 1 ↔ (v : G) ∈ centralizer ({t} : Set G)
    rw [commutatorElement_eq_one_iff_mul_comm,mem_centralizer_singleton_iff]
  change ((centralizer ({t} : Set G)).subgroupOf V).index ≤ _
  rw [←hk,index_ker]
  exact Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective

theorem abelian_singleton_centralizer_eq_intersection
    (V Q Z K : Subgroup G) [Finite V] [Finite Z] [IsMulCommutative V]
    (hZ : Z ≤ V) (hcomm : ⁅V,Q⁆ ≤ Z) {t : G} (ht : t ∈ Q)
    (hindex : K.relIndex V = Nat.card Z)
    (htrapped : V ⊓ centralizer ({t} : Set G) ≤ K) :
    V ⊓ centralizer ({t} : Set G) = V ⊓ K := by
  let A := V ⊓ centralizer ({t} : Set G)
  let B := V ⊓ K
  have hAB : A ≤ B := le_inf inf_le_left htrapped
  have hi : A.relIndex V ≤ B.relIndex V := by
    rw [inf_relIndex_left,inf_relIndex_left,hindex]
    exact abelian_singleton_centralizer_index_le V Q Z hZ hcomm ht
  let : Finite A := Finite.of_injective (inclusion (show A ≤ V from inf_le_left))
    (inclusion_injective _)
  let : Finite B := Finite.of_injective (inclusion (show B ≤ V from inf_le_left))
    (inclusion_injective _)
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup G) A V bot_le inf_le_left
  have hmul' := relIndex_mul_relIndex (⊥ : Subgroup G) B V bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left] at hmul hmul'
  have hp : 0 < B.relIndex V := Nat.pos_of_ne_zero index_ne_zero_of_finite
  apply eq_of_le_of_card_ge hAB
  have hh : Nat.card B * B.relIndex V ≤ Nat.card A * B.relIndex V := by
    rw [hmul',←hmul]
    exact Nat.mul_le_mul_left _ hi
  exact Nat.le_of_mul_le_mul_right hh hp
end Subgroup
