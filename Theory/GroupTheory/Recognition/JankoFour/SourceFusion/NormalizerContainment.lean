module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.FixedCoset
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.FixedCosetCriterion
/-!
# Pair-plane normalizer containment

The actual quotient E/U has order 512. Transitivity on its 511 nonidentity
elements would force 511 to divide the original Todd group order, which
it does not. Unique fixed cosets therefore force N_I(U) into M for every
pure pair plane through t, with I=C_G(t). If E meets E^g in such a plane,
then E^g lies in that normalizer and violates its elementary subgroup bound.
Consequently an escaping conjugate radical meets E only in the t-line.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), proof of (6.3), p.602.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

theorem point_group_card (a : LocalData h) : Nat.card a.P.M = 2^11 * 244823040 := by
  rw [←Nat.card_congr a.P.toddEquiv.toEquiv]
  change Nat.card (ToddVector ⋊[toddAction] M24) = _
  rw [SemidirectProduct.card,m24_order]
  have hv : Nat.card ToddVector = 2^11 :=
    (Nat.card_congr a.P.vectorEquiv.toEquiv).trans a.P.E_card
  rw [hv]

theorem purePairNormalizer_le (a : LocalData h) (hi : MarkerIntersection a)
    (W : Subgroup G) (hWE : W ≤ a.P.E) (ht : second a ∈ W) (hc : 2 < Nat.card W)
    (hp : ∀ u ∈ W, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u) :
    normalizer (W : Set G) ⊓ centralizer (second a) ≤ a.P.M := by
  let N := normalizer (W : Set G) ⊓ centralizer (second a)
  let M := a.P.M.subgroupOf N
  let B := a.P.E.subgroupOf N
  let U := W.subgroupOf N
  have hEN : a.P.E ≤ N := fun x hx =>
    ⟨(E_le_pairNormalizer a _ hWE hx).1,
      (E_le_pairNormalizer a _ hWE hx).2.1⟩
  have hUN : W ≤ N := hWE.trans hEN
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (show N ≤ normalizer (W : Set G) from inf_le_left)
  have hBM : B ≤ M := fun _ hx => a.P.E_le hx
  have hBN : (B.subgroupOf M).Normal := by
    apply (normal_subgroupOf_iff hBM).mpr
    intro b m hb hm
    exact (mem_normalizer_iff.mp (a.point_normalizer.symm ▸ (show m.val ∈ a.P.M from hm)) b.val).mp hb
  have hBc : Nat.card B = 2^11 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).trans a.P.E_card
  have hUc : Nat.card U = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv).trans (pair_subgroup_card_eq_four a W hWE hc hp)
  have hdM : Nat.card M ∣ Nat.card a.P.M := by
    let f : M →* a.P.M := {
      toFun := fun x => ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    apply card_dvd_of_injective f
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : a.P.M => q.val) he
  apply subgroupOf_eq_top.mp
  change M = ⊤
  let := a.P.E_elementary
  apply fixed_coset_quotient_eq_top M B U (comap_mono hWE) hBM hBN
    (fun b hb => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian b.val (show b.val ∈ a.P.E from hb)))
  · rw [hBc,hUc]
    decide
  · rw [hBc,hUc]
    intro hd
    have he := hd.trans hdM
    rw [point_group_card] at he
    exact (by decide : ¬ (2^11 / 4 - 1) ∣ 2^11 * 244823040) he
  · intro b hb hbU
    exact purePair_unique_fixed_coset a hi W hWE ht hc hp b hb hbU


theorem pairAmbientNormalizer_le (a : LocalData h) (hi : MarkerIntersection a) :
    pairAmbientNormalizer a ≤ a.P.M :=
  purePairNormalizer_le a hi (secondPlane a) (secondPlane_le a)
    (second_mem_secondPlane a) (by rw [secondPlane_card]; decide) (secondPlane_orbit a)

/-- Once every pair-plane normalizer is contained, escaping radicals meet only
in the distinguished involution line. -/
theorem centralizer_intersection_card_le_two (a : LocalData h) (hi : MarkerIntersection a)
    (g : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M) :
    Nat.card (a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 := by
  let := a.P.E_elementary
  let F := a.P.E.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  let U := a.P.E ⊓ F
  have htF : second a ∈ F := ⟨second a,second_mem a,
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgc)⟩
  have htU : second a ∈ U := ⟨second_mem a,htF⟩
  have hp := centralizer_intersection_second a hi g hgc hgm
  by_contra hnot
  have hc : 2 < Nat.card U := by
    change ¬ Nat.card U ≤ 2 at hnot
    omega
  have hN := purePairNormalizer_le a hi U inf_le_left htU hc hp
  have hFN : F ≤ pairNormalizer a U := by
    intro x hx
    have hxU : x ∈ Subgroup.centralizer (U : Set G) := by
      intro u hu
      exact congrArg Subtype.val (mul_comm (⟨u,hu.2⟩ : F) ⟨x,hx⟩)
    have hxI : x ∈ centralizer (second a) :=
      mem_centralizer_singleton_iff.mpr (setLike_mul_comm hx htF)
    have hxN := Subgroup.centralizer_le_normalizer _ hxU
    exact ⟨hxN,hxI,hN ⟨hxN,hxI⟩⟩
  have hb := purePairNormalizer_conjugate_subgroup_card_le a hi U inf_le_left htU hc hp
    g hgc hgm F hFN le_rfl
  have hFcard : Nat.card F = 2^11 :=
    (card_map_of_injective (MulAut.conj g).injective).trans a.P.E_card
  omega

theorem second_strict_overgroup_normalizer_le (a : LocalData h) (hi : MarkerIntersection a)
    (V : Subgroup G) (hVE : V ≤ a.P.E) (hc : 2 < Nat.card V) :
    normalizer (V : Set G) ⊓ centralizer (second a) ≤ a.P.M := by
  intro g hg
  by_contra hgm
  have hVg : V ≤ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom := by
    refine le_inf hVE ?_
    have he := mem_normalizer_iff_map_conj_eq.mp hg.1
    rw [←he]
    exact map_mono hVE
  have hb := (card_le_of_le hVg).trans
    (centralizer_intersection_card_le_two a hi g hg.2 hgm)
  omega


/-- The sharp intersection is the literal cyclic subgroup of t. -/
theorem centralizer_intersection_eq_second_line (a : LocalData h) (hi : MarkerIntersection a)
    (g : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M) :
    a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom = zpowers (second a) := by
  have ht : second a ∈ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom :=
    ⟨second_mem a,second a,second_mem a,
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgc)⟩
  apply (eq_of_le_of_card_ge (zpowers_le.mpr ht) ?_).symm
  rw [Nat.card_zpowers,second_order]
  exact centralizer_intersection_card_le_two a hi g hgc hgm

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
