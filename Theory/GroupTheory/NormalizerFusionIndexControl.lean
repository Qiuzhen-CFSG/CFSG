module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group

/-!
# Normalizer fusion when the outer index is realized internally

Let `U ≤ P ≤ G`, with `G` finite. Write `N = N_G(U)` and
`D = U C_G(U)`. If `[P ∩ N : P ∩ D] = [N : D]`, every ambient
normalizer conjugacy between elements of `U` is already conjugacy inside
`P`. The equality of indices says that the internal normalizer realizes all
outer actions; the inner actions of `U` also come from `P` because `U ≤ P`.
No Sylow or extremality hypothesis is needed.

Work inside `N`, where the copy of `D` is normal. The relative-index formula
for a join with a normal subgroup, followed by index multiplicativity, shows
that `D` together with `P ∩ N` generates `N`. Decompose a normalizer element
as `u c s`, with `u ∈ U`, `c ∈ C_G(U)`, and `s ∈ P ∩ N`. The centralizer
factor fixes `u⁻¹ x u`, so right conjugation is a composition of two
conjugacies inside `P`.

This supplies the index-two local-action cases of Alperin–Brauer–Gorenstein
Chapter II §1, Proposition 1 (article pp.10–11): the four and quaternion-eight
representatives have internal outer normalizer index two. The generic result
here applies whenever the internal and ambient indices agree.

The denominator restriction lemma expresses the self-centralizing case:
if `C_P(U) ≤ U`, then `(U C_G(U)) ∩ P = U`. Write an element as `u c`;
since both it and `u` lie in `P`, the centralizer factor also lies in `P`
and hence in `U`. This allows source consumers to replace the internal
outer index with the internal normalizer index of `U`.
-/

namespace Subgroup

/-- If the centralizer of `U` inside `P` lies in `U`, restricting the outer
automizer denominator `U ⊔ C_G(U)` to `P` leaves precisely `U`. -/
public theorem sup_centralizer_subgroupOf_eq_of_centralizer_le
    {G : Type*} [Group G] (P U : Subgroup G) (hUP : U ≤ P)
    (hC : (centralizer (U : Set G)).subgroupOf P ≤ U.subgroupOf P) :
    (U ⊔ centralizer (U : Set G)).subgroupOf P = U.subgroupOf P := by
  apply le_antisymm
  · intro x hx
    change (x : G) ∈ U
    change (x : G) ∈ U ⊔ centralizer (U : Set G) at hx
    have he := coe_mul_of_right_le_normalizer_left U
      (centralizer (U : Set G)) (centralizer_le_normalizer (U : Set G))
    rw [← SetLike.mem_coe, he] at hx
    obtain ⟨u, hu, c, hc, huc⟩ := hx
    have hcP : c ∈ P := by
      have ht := P.mul_mem (P.inv_mem (hUP hu)) x.property
      rw [← huc, inv_mul_cancel_left] at ht
      exact ht
    have hcU : c ∈ U := hC
      (show (⟨c, hcP⟩ : P) ∈ (centralizer (U : Set G)).subgroupOf P from hc)
    rw [← huc]
    exact U.mul_mem hu hcU
  · intro x hx
    exact (le_sup_left : U ≤ U ⊔ centralizer (U : Set G)) hx

/-- If the internal normalizer realizes the ambient outer normalizer index,
normalizer fusion at a contained subgroup is already conjugacy inside `P`. -/
public theorem normalizer_fusion_control_of_outer_index_eq
    {G : Type*} [Group G] [Finite G] (P U : Subgroup G) (hUP : U ≤ P)
    (hindex :
      ((U ⊔ centralizer (U : Set G)).subgroupOf P).relIndex
          ((normalizer (U : Set G)).subgroupOf P) =
        (U ⊔ centralizer (U : Set G)).relIndex (normalizer (U : Set G)))
    (g : G) (hg : g ∈ normalizer (U : Set G))
    (x y : P) (hxU : (x : G) ∈ U)
    (hxy : g⁻¹ * (x : G) * g = (y : G)) : IsConj x y := by
  let N : Subgroup G := normalizer (U : Set G)
  let C : Subgroup G := centralizer (U : Set G)
  let D : Subgroup G := U ⊔ C
  let UN : Subgroup N := U.subgroupOf N
  let CN : Subgroup N := C.subgroupOf N
  let DN : Subgroup N := D.subgroupOf N
  let PN : Subgroup N := P.subgroupOf N
  have hUN : U ≤ N := le_normalizer
  have hCN : C ≤ N := centralizer_le_normalizer _
  have hDN : DN = UN ⊔ CN := subgroupOf_sup hUN hCN
  have : UN.Normal := inferInstanceAs ((U.subgroupOf (normalizer (U : Set G))).Normal)
  have : CN.Normal := normal_subgroupOf_centralizer_normalizer (U : Set G)
  have : DN.Normal := by rw [hDN]; infer_instance
  have hrel : DN.relIndex PN = DN.index := by
    change (D.subgroupOf N).relIndex (P.subgroupOf N) = D.relIndex N
    rw [subgroupOf, relIndex_comap, subgroupOf_map_subtype]
    have hi := hindex
    change (D.subgroupOf P).relIndex (N.subgroupOf P) = D.relIndex N at hi
    rw [subgroupOf, relIndex_comap, subgroupOf_map_subtype] at hi
    simpa only [inf_comm] using hi
  have hsuptop : DN ⊔ PN = ⊤ := by
    have hmul := relIndex_mul_index (le_sup_left : DN ≤ DN ⊔ PN)
    rw [relIndex_sup_left, hrel] at hmul
    have hne : DN.index ≠ 0 := FiniteIndex.index_ne_zero
    have hi : (DN ⊔ PN).index = 1 := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
      simpa using hmul
    exact index_eq_one.mp hi
  let gN : N := ⟨g, hg⟩
  have hgSup : gN ∈ DN ⊔ PN := by rw [hsuptop]; trivial
  obtain ⟨d, hd, s, hs, hdsg⟩ := mem_sup_of_normal_left.mp hgSup
  rw [hDN] at hd
  obtain ⟨u, hu, c, hc, hucd⟩ := mem_sup_of_normal_right.mp hd
  have huU : (u : G) ∈ U := hu
  have hcC : (c : G) ∈ C := hc
  have hsP : (s : G) ∈ P := hs
  let uP : P := ⟨u, hUP huU⟩
  let sP : P := ⟨s, hsP⟩
  let x' : P := uP⁻¹ * x * uP
  have hx'U : (x' : G) ∈ U := U.mul_mem (U.mul_mem (U.inv_mem huU) hxU) huU
  have hcfix : (c : G)⁻¹ * (x' : G) * (c : G) = (x' : G) := by
    have hcomm := mem_centralizer_iff.mp hcC (x' : G) hx'U
    rw [mul_assoc, hcomm]
    simp
  have hgval : g = (u : G) * (c : G) * (s : G) := by
    have hh := congrArg Subtype.val hdsg
    rw [← hucd] at hh
    exact hh.symm
  have hsxy : (s : G)⁻¹ * (x' : G) * (s : G) = (y : G) := by
    calc
      _ = (s : G)⁻¹ * ((c : G)⁻¹ * (x' : G) * (c : G)) * (s : G) := by rw [hcfix]
      _ = g⁻¹ * (x : G) * g := by
        rw [hgval]
        change (s : G)⁻¹ * ((c : G)⁻¹ * ((u : G)⁻¹ * (x : G) * (u : G)) * (c : G)) * (s : G) = _
        group
      _ = (y : G) := hxy
  have hxx' : IsConj x x' := isConj_iff.mpr ⟨uP⁻¹, by simp [x']⟩
  apply hxx'.trans
  apply isConj_iff.mpr
  refine ⟨sP⁻¹, ?_⟩
  apply Subtype.ext
  simpa [sP] using hsxy

end Subgroup
