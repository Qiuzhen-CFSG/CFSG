module
public import Theory.GroupTheory.AbelianCommutatorIndex

/-!
# A line of commutators on an index-two subgroup

On an abelian group, the commutator map of a normalizing element is a
homomorphism. If its restriction to an index-two subgroup has image of
order at most two, its fixed subgroup has index at most four. Passing to
the literal normal quotient proves the same statement when only the
quotient of the original numerator is abelian.

Source application: Aschbacher--Smith, Lemma 13.8.33, printed p.967,
with numerator V_H, lower subgroup U_H and image line VU_H/U_H.
-/

public section
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An element whose movement on an index-two subgroup of an abelian
group lies in a two-element subgroup has fixed index at most four. -/
theorem centralizer_relIndex_le_four_of_index_two
    (X U W : Subgroup G) [IsMulCommutative U] (hXU : X ≤ U)
    (y : G) (hy : y ∈ normalizer (U : Set G))
    (hc : ∀ x ∈ X, ⁅x,y⁆ ∈ W) (hW : Nat.card W ≤ 2)
    (hindex : X.relIndex U ≤ 2) :
    (centralizer (zpowers y : Set G)).relIndex U ≤ 4 := by
  rw [zpowers_eq_closure, centralizer_closure]
  let C := centralizer ({y} : Set G)
  have hsmall : C.relIndex X ≤ 2 :=
    (centralizer_relIndex_le_card_of_abelian_commutator X U W hXU y hy hc).trans hW
  have hm := relIndex_inf_mul_relIndex C X U
  rw [inf_of_le_left hXU] at hm
  have hle : C.relIndex U ≤ (C ⊓ X).relIndex U :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  change C.relIndex U ≤ 4
  calc
    C.relIndex U ≤ (C ⊓ X).relIndex U := hle
    _ = C.relIndex X * X.relIndex U := hm.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hsmall hindex

/-- The same bound for the literal normal quotient. Neither the original
numerator nor the index-two subgroup is assumed abelian. -/
theorem quotient_centralizer_relIndex_le_four_of_index_two
    (V Z X W : Subgroup G) [V.Normal] [Z.Normal]
    (hZV : Z ≤ V) (hXV : X ≤ V) (habelian : ⁅V,V⁆ ≤ Z)
    (y : G) (hc : ⁅X,zpowers y⁆ ≤ W)
    (hW : Z.relIndex W ≤ 2) (hindex : X.relIndex V ≤ 2) :
    (centralizer (zpowers (QuotientGroup.mk' Z y) : Set (G ⧸ Z))).relIndex
      (V.map (QuotientGroup.mk' Z)) ≤ 4 := by
  let π := QuotientGroup.mk' Z
  let Vbar := V.map π
  let Xbar := X.map π
  let Wbar := W.map π
  let : Vbar.Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  let : IsMulCommutative Vbar := by
    apply commutator_self_eq_bot_iff.mp
    rw [← map_commutator]
    apply (map_eq_bot_iff (f := π) _).mpr
    simpa only [π, QuotientGroup.ker_mk'] using habelian
  have hcbar : ⁅Xbar,zpowers (π y)⁆ ≤ Wbar := by
    have hh := map_mono (f := π) hc
    rwa [map_commutator, MonoidHom.map_zpowers] at hh
  have hWbar : Nat.card Wbar ≤ 2 := by
    rw [← relIndex_ker, show π.ker = Z from QuotientGroup.ker_mk' Z]
    exact hW
  have hi : Xbar.relIndex Vbar ≤ 2 := by
    rw [relIndex_map_map, show π.ker = Z from QuotientGroup.ker_mk' Z,
      sup_of_le_left hZV]
    exact (relIndex_le_of_le_left le_sup_left index_ne_zero_of_finite).trans hindex
  exact centralizer_relIndex_le_four_of_index_two Xbar Vbar Wbar (map_mono hXV)
    (π y) (by rw [normalizer_eq_top]; trivial) (fun x hx => hcbar
      (commutator_mem_commutator hx (mem_zpowers (π y)))) hWbar hi
end Subgroup
