module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.SecondFixedCoset
/-!
# The full second involution centralizer and the unique radical

The second fixed-coset argument applies to the original I=C_G(t).
The 1023 nonidentity elements of E/<t> cannot form a single orbit under
I∩M, since 1023 does not divide the Todd group order. The normal binary
quotient criterion gives I≤M. The two Todd orbits and ambient nonfusion
then show that any conjugate of E containing t is E itself.

Only the exact earlier marker-intersection premise is conditional.
Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.3)(3), p.602.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

theorem second_centralizer_le (a : LocalData h) (hi : MarkerIntersection a) :
    centralizer (second a) ≤ a.P.M := by
  let N := centralizer (second a)
  let M := a.P.M.subgroupOf N
  let B := a.P.E.subgroupOf N
  let U := (zpowers (second a)).subgroupOf N
  let := a.P.E_elementary
  have hEN : a.P.E ≤ N := fun x hx =>
    mem_centralizer_singleton_iff.mpr (setLike_mul_comm hx (second_mem a))
  have hUE : zpowers (second a) ≤ a.P.E := zpowers_le.mpr (second_mem a)
  have hUN : zpowers (second a) ≤ N := hUE.trans hEN
  let : U.Normal := normal_subgroupOf_of_le_normalizer (by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    congr 1
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg))
  have hBM : B ≤ M := fun _ hx => a.P.E_le hx
  have hBN : (B.subgroupOf M).Normal := by
    apply (normal_subgroupOf_iff hBM).mpr
    intro b m hb hm
    exact (mem_normalizer_iff.mp (a.point_normalizer.symm ▸ (show m.val ∈ a.P.M from hm)) b.val).mp hb
  have hBc : Nat.card B = 2^11 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).trans a.P.E_card
  have hUc : Nat.card U = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv,Nat.card_zpowers,second_order]
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
  apply fixed_coset_quotient_eq_top M B U (comap_mono hUE) hBM hBN
    (fun b hb => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian b.val (show b.val ∈ a.P.E from hb)))
  · rw [hBc,hUc]
    decide
  · rw [hBc,hUc]
    intro hd
    have he := hd.trans hdM
    rw [point_group_card] at he
    exact (by decide : ¬ (2^11 / 2 - 1) ∣ 2^11 * 244823040) he
  · intro b hb hbU
    exact second_unique_fixed_coset a hi b hb hbU

/-- AS91 (6.3)(3): the original point-group centralizer is the full centralizer. -/
theorem second_centralizer_eq (a : LocalData h) (hi : MarkerIntersection a) :
    centralizer (second a) = secondCentralizer a :=
  le_antisymm (le_inf le_rfl (second_centralizer_le a hi)) inf_le_left

/-- Any conjugate of the original radical containing t is that same radical. -/
theorem second_radical_unique (a : LocalData h) (hi : MarkerIntersection a)
    (g : G) (ht : second a ∈ a.P.E.map (MulAut.conj g).toMonoidHom) :
    a.P.E.map (MulAut.conj g).toMonoidHom = a.P.E := by
  obtain ⟨v,hv,hvt⟩ := ht
  change MulAut.conj g v = second a at hvt
  have hv1 : v ≠ 1 := by
    intro he
    rw [he,map_one] at hvt
    exact second_ne_one a hvt.symm
  rcases E_orbits a v hv hv1 with ⟨m,hm,hmv⟩ | ⟨m,hm,hmv⟩
  · exact (not_isConj_second a
      ((isConj_iff.mpr ⟨m,hmv⟩).trans (isConj_iff.mpr ⟨g,hvt⟩))).elim
  · have hgm : g*m ∈ centralizer (second a) := by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        (g*m)*second a*(g*m)⁻¹ = g*(m*second a*m⁻¹)*g⁻¹ := by group
        _ = second a := by rw [show m*second a*m⁻¹ = v from hmv]; exact hvt
    have hgM : g ∈ a.P.M := by
      have hh := a.P.M.mul_mem (second_centralizer_le a hi hgm) (a.P.M.inv_mem hm)
      simpa only [mul_inv_cancel_right] using hh
    rw [←a.point_normalizer] at hgM
    exact mem_normalizer_iff_map_conj_eq.mp hgM

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
