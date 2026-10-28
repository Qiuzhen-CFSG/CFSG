module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Action
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# The two marked transvections in the PGL₂ shadow

Work inside the actual ambient elementary eight V. Weak closure on the two
axes excludes either center lying in the other axis. Enumerating the eight
products of r,z,v then forces u = rzv. The conjugator s*t fuses u to v, the
common fixed line is ⟨vz⟩ = ⟨ur⟩, and ⟨u,v⟩ is its direct complement in V.
An additional conjugation fixing z,v and sending r to rz would fuse z to u,
and hence to v, contrary to weak closure.

These are conditional ambient calculations. Construction of the configuration,
the local fusion in T_L⟨u⟩, and the transfer quotients are separate obligations.
The conclusions do not rely on an abstract group-family label or on an assumed
prohibited-fusion statement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 16.4.6,
printed pp.1185–1186. All conjugations here are left conjugations.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections
variable {G : Type*} [Group G] [Finite G]

private theorem mem_two {a x : G} (ha : orderOf a = 2) :
    x ∈ zpowers a ↔ x = 1 ∨ x = a := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ha]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, hn'⟩
    interval_cases n <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩

omit [Finite G] in
private theorem commute_in {V : Subgroup G} [IsMulCommutative V]
    {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x :=
  congrArg Subtype.val (mul_comm (⟨x, hx⟩ : V) ⟨y, hy⟩)

omit [Finite G] in
private theorem split_join {V A B : Subgroup G} [IsMulCommutative V]
    (hA : A ≤ V) (hB : B ≤ V) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hn : B ≤ normalizer (A : Set G) := by
    intro b hb
    apply Subgroup.centralizer_le_normalizer
    exact mem_centralizer_iff.mpr (fun a ha => commute_in (hA ha) (hB hb))
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hn]
    exact hx
  exact hx'

private theorem pair_cases {V : Subgroup G} [IsMulCommutative V]
    {a b x : G} (ha : a ∈ V) (hb : b ∈ V)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (hx : x ∈ zpowers a ⊔ zpowers b) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  obtain ⟨c, hc, d, hd, rfl⟩ := split_join (zpowers_le.mpr ha) (zpowers_le.mpr hb) hx
  rcases (mem_two ha2).mp hc with rfl | rfl <;>
    rcases (mem_two hb2).mp hd with rfl | rfl <;> simp

private theorem eight_cases {V : Subgroup G} [IsMulCommutative V]
    {r z v x : G} (hr : r ∈ V) (hz : z ∈ V) (hv : v ∈ V)
    (hr2 : orderOf r = 2) (hz2 : orderOf z = 2) (hv2 : orderOf v = 2)
    (hspan : V = zpowers r ⊔ (zpowers z ⊔ zpowers v)) (hx : x ∈ V) :
    x = 1 ∨ x = z ∨ x = v ∨ x = z * v ∨
    x = r ∨ x = r * z ∨ x = r * v ∨ x = r * (z * v) := by
  have hx' : x ∈ zpowers r ⊔ (zpowers z ⊔ zpowers v) := hspan ▸ hx
  obtain ⟨a, ha, b, hb, rfl⟩ := split_join (zpowers_le.mpr hr)
    (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hv)) hx'
  rcases (mem_two hr2).mp ha with rfl | rfl <;>
    rcases pair_cases hz hv hz2 hv2 hb with rfl | rfl | rfl | rfl <;> simp

/-- Weak closure on a specified ambient subgroup, for one element. -/
def WeaklyClosed (a : G) (A : Subgroup G) : Prop :=
  ∀ x ∈ A, IsConj a x → x = a

/-- The marked eight and the two actual conjugation actions. The weak-closure
premises concern the two axes; no fusion or quotient conclusion is included. -/
structure EightConfig (V : Subgroup G) (r z v u s t : G) : Prop where
  elementary : IsElementaryAbelian 2 V
  card : Nat.card V = 8
  r_mem : r ∈ V
  z_mem : z ∈ V
  v_mem : v ∈ V
  u_mem : u ∈ V
  r_order : orderOf r = 2
  z_order : orderOf z = 2
  v_order : orderOf v = 2
  u_order : orderOf u = 2
  span : V = zpowers r ⊔ (zpowers z ⊔ zpowers v)
  u_ne_v : u ≠ v
  u_ne_r : u ≠ r
  s_normalizes : s ∈ normalizer (V : Set G)
  t_normalizes : t ∈ normalizer (V : Set G)
  t_r : MulAut.conj t r = r * v
  t_z : MulAut.conj t z = z
  t_v : MulAut.conj t v = v
  s_z : MulAut.conj s z = z * u
  s_r : MulAut.conj s r = r
  s_u : MulAut.conj s u = u
  weak_z : WeaklyClosed z (zpowers z ⊔ zpowers v)
  weak_r : WeaklyClosed r (zpowers r ⊔ zpowers u)

namespace EightConfig
variable {V : Subgroup G} {r z v u s t : G} (h : EightConfig V r z v u s t)
include h

omit [Finite G] in
/-- A transvection with center in the other axis would move a weakly closed point
within that axis. This excludes the first dihedral arrangement. -/
theorem u_not_mem_axis : u ∉ zpowers z ⊔ zpowers v := by
  intro hu
  have he := h.weak_z (z * u)
    ((zpowers z ⊔ zpowers v).mul_mem (mem_sup_left (mem_zpowers z)) hu)
    (isConj_iff.mpr ⟨s, h.s_z⟩)
  have hu1 : u = 1 := mul_left_cancel (he.trans (mul_one z).symm)
  simpa [hu1] using h.u_order

omit [Finite G] in
/-- Symmetric exclusion of the other dihedral arrangement. -/
theorem v_not_mem_axis : v ∉ zpowers r ⊔ zpowers u := by
  intro hv
  have he := h.weak_r (r * v)
    ((zpowers r ⊔ zpowers u).mul_mem (mem_sup_left (mem_zpowers r)) hv)
    (isConj_iff.mpr ⟨t, h.t_r⟩)
  have hv1 : v = 1 := mul_left_cancel (he.trans (mul_one r).symm)
  simpa [hv1] using h.v_order

/-- The two weak closures force the source's marked relation `u = rzv`. -/
theorem u_eq : u = r * (z * v) := by
  let := h.elementary
  have hu := eight_cases h.r_mem h.z_mem h.v_mem h.r_order h.z_order h.v_order h.span h.u_mem
  rcases hu with hu | hu | hu | hu | hu | hu | hu | hu
  · exact False.elim (h.u_not_mem_axis (hu ▸ (zpowers z ⊔ zpowers v).one_mem))
  · exact False.elim (h.u_not_mem_axis (by rw [hu]; exact mem_sup_left (mem_zpowers z)))
  · exact False.elim (h.u_ne_v hu)
  · exact False.elim (h.u_not_mem_axis (by rw [hu]; exact mul_mem_sup (mem_zpowers z) (mem_zpowers v)))
  · exact False.elim (h.u_ne_r hu)
  · have hs := h.s_u
    rw [hu, map_mul, h.s_r, h.s_z] at hs
    have hzu : z * u = z := mul_left_cancel hs
    have hu1 : u = 1 := mul_left_cancel (hzu.trans (mul_one z).symm)
    simpa [hu1] using h.u_order
  · apply False.elim
    apply h.v_not_mem_axis
    have hr2 : r * r = 1 := by simpa only [h.r_order, pow_two] using pow_orderOf_eq_one r
    have he : v = r * u := by rw [hu, ← mul_assoc, hr2, one_mul]
    rw [he]
    exact mul_mem_sup (mem_zpowers r) (mem_zpowers u)
  · exact hu

/-- The common fixed line has the two source markings. -/
theorem fixed_line_relation : v * z = u * r := by
  let := h.elementary
  have hr2 : r * r = 1 := by simpa only [h.r_order, pow_two] using pow_orderOf_eq_one r
  rw [h.u_eq, mul_assoc, ← commute_in h.r_mem (V.mul_mem h.z_mem h.v_mem),
    ← mul_assoc, hr2, one_mul, commute_in h.z_mem h.v_mem]

omit [Finite G] in
private theorem sq (x : G) (hx : x ∈ V) : x * x = 1 := by
  let := h.elementary
  simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx

omit [Finite G] in
private theorem comm {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x := by
  let := h.elementary
  exact commute_in hx hy

/-- The first transvection interchanges the other two nonidentity plane points. -/
theorem t_u : MulAut.conj t u = u * v := by
  rw [h.u_eq, map_mul, map_mul, h.t_r, h.t_z, h.t_v]
  rw [mul_assoc, h.comm h.v_mem (V.mul_mem h.z_mem h.v_mem), ← mul_assoc]

/-- The symmetric transvection interchanges the other two plane points. -/
theorem s_v : MulAut.conj s v = u * v := by
  have hs := h.s_u
  rw [h.u_eq, map_mul, map_mul, h.s_r, h.s_z] at hs
  have hh : u * MulAut.conj s v = v := by
    apply mul_left_cancel (a := z)
    apply mul_left_cancel (a := r)
    simpa only [mul_assoc] using hs
  calc
    MulAut.conj s v = u * (u * MulAut.conj s v) := by rw [← mul_assoc, h.sq u h.u_mem, one_mul]
    _ = u * v := by rw [hh]

/-- The conjugator `s*t` explicitly fuses the two centers. -/
theorem u_fused_v : IsConj u v := by
  apply isConj_iff.mpr
  refine ⟨s * t, ?_⟩
  have he : MulAut.conj s (MulAut.conj t u) = v := by
    rw [h.t_u, map_mul, h.s_u, h.s_v, ← mul_assoc, h.sq u h.u_mem, one_mul]
  simpa only [MulAut.conj_apply, mul_inv_rev, mul_assoc] using he

/-- Both actual conjugators fix `vz`. -/
theorem fixed_product : MulAut.conj t (v * z) = v * z ∧
    MulAut.conj s (v * z) = v * z := by
  constructor
  · rw [map_mul, h.t_v, h.t_z]
  · rw [map_mul, h.s_v, h.s_z, h.comm h.u_mem h.v_mem]
    calc
      v * u * (z * u) = v * (u * z) * u := by group
      _ = v * (z * u) * u := by rw [h.comm h.u_mem h.z_mem]
      _ = v * z := by rw [mul_assoc, mul_assoc, h.sq u h.u_mem, mul_one]

/-- Weak closure separates the two ambient classes used in the transfer ending. -/
theorem z_not_fused_v : ¬ IsConj z v := by
  intro hzv
  have hvz := h.weak_z v (mem_sup_right (mem_zpowers v)) hzv
  apply h.u_ne_r
  rw [h.u_eq, ← hvz, h.sq v h.v_mem, mul_one]

/-- An additional transvection centered at z forces forbidden fusion. The local
subgroup argument remains responsible for constructing its actual conjugator. -/
theorem no_extra_transvection (a : G)
    (ha_r : MulAut.conj a r = r * z)
    (ha_z : MulAut.conj a z = z) (ha_v : MulAut.conj a v = v) : False := by
  have hau : MulAut.conj a u = z * u := by
    rw [h.u_eq, map_mul, map_mul, ha_r, ha_z, ha_v]
    rw [← mul_assoc z r, h.comm h.z_mem h.r_mem, mul_assoc]
  have hzu : IsConj z u := (isConj_iff.mpr ⟨s, h.s_z⟩).trans
    (isConj_iff.mpr ⟨a, hau⟩).symm
  exact h.z_not_fused_v (hzu.trans h.u_fused_v)

/-- The common fixed points are precisely the source line `⟨vz⟩`. -/
theorem common_fixed_iff (x : G) (hx : x ∈ V) :
    (MulAut.conj t x = x ∧ MulAut.conj s x = x) ↔ x = 1 ∨ x = v * z := by
  let := h.elementary
  have hv1 : v ≠ 1 := by intro he; simpa [he] using h.v_order
  have hu1 : u ≠ 1 := by intro he; simpa [he] using h.u_order
  have hmoved (a : G) (ha : MulAut.conj t a = a) :
      MulAut.conj t (r * a) ≠ r * a := by
    intro he
    rw [map_mul, h.t_r, ha] at he
    exact hv1 (mul_left_cancel ((mul_right_cancel he).trans (mul_one r).symm))
  constructor
  · rintro ⟨htx, hsx⟩
    rcases eight_cases h.r_mem h.z_mem h.v_mem h.r_order h.z_order h.v_order h.span hx with
      he | he | he | he | he | he | he | he
    · exact Or.inl he
    · subst x
      rw [h.s_z] at hsx
      exact False.elim (hu1 (mul_left_cancel (hsx.trans (mul_one z).symm)))
    · subst x
      rw [h.s_v] at hsx
      exact False.elim (hu1 (mul_right_cancel (hsx.trans (one_mul v).symm)))
    · exact Or.inr (he.trans (h.comm h.z_mem h.v_mem))
    · subst x
      have hh := hmoved 1 (map_one (MulAut.conj t))
      simp only [mul_one] at hh
      exact False.elim (hh htx)
    · subst x
      exact False.elim (hmoved z h.t_z htx)
    · subst x
      exact False.elim (hmoved v h.t_v htx)
    · subst x
      exact False.elim (hmoved (z * v) (by rw [map_mul, h.t_z, h.t_v]) htx)
  · rintro (rfl | rfl)
    · simp
    · exact h.fixed_product

/-- The invariant plane and common fixed line generate the actual eight. -/
theorem plane_sup_line :
    (zpowers u ⊔ zpowers v) ⊔ zpowers (v * z) = V := by
  apply le_antisymm
  · exact sup_le (sup_le (zpowers_le.mpr h.u_mem) (zpowers_le.mpr h.v_mem))
      (zpowers_le.mpr (V.mul_mem h.v_mem h.z_mem))
  · rw [h.span]
    let W := (zpowers u ⊔ zpowers v) ⊔ zpowers (v * z)
    have huW : u ∈ W := mem_sup_left (mem_sup_left (mem_zpowers u))
    have hvW : v ∈ W := mem_sup_left (mem_sup_right (mem_zpowers v))
    have hwW : v * z ∈ W := mem_sup_right (mem_zpowers (v * z))
    have hr : r = u * (v * z) := by
      rw [h.fixed_line_relation, ← mul_assoc, h.sq u h.u_mem, one_mul]
    have hz : z = v * (v * z) := by rw [← mul_assoc, h.sq v h.v_mem, one_mul]
    exact sup_le (zpowers_le.mpr (Eq.mpr (congrArg (fun x : G => x ∈ W) hr) (W.mul_mem huW hwW)))
      (sup_le (zpowers_le.mpr (Eq.mpr (congrArg (fun x : G => x ∈ W) hz) (W.mul_mem hvW hwW))) (zpowers_le.mpr hvW))

/-- The invariant plane and the fixed line meet trivially. Together with
`plane_sup_line`, this is the source direct-sum decomposition of V. -/
theorem plane_disjoint_line :
    Disjoint (zpowers u ⊔ zpowers v) (zpowers (v * z)) := by
  let := h.elementary
  apply Subgroup.disjoint_def.mpr
  intro x hx hxline
  have ht : MulAut.conj t x = x := by
    exact (MulAut.mem_fixedSubgroup _ _).mp ((zpowers_le.mpr
      ((MulAut.mem_fixedSubgroup _ _).mpr h.fixed_product.1)) hxline)
  have hs : MulAut.conj s x = x := by
    exact (MulAut.mem_fixedSubgroup _ _).mp ((zpowers_le.mpr
      ((MulAut.mem_fixedSubgroup _ _).mpr h.fixed_product.2)) hxline)
  have hv1 : v ≠ 1 := by intro he; simpa [he] using h.v_order
  have hu1 : u ≠ 1 := by intro he; simpa [he] using h.u_order
  rcases pair_cases h.u_mem h.v_mem h.u_order h.v_order hx with he | he | he | he
  · exact he
  · subst x
    rw [h.t_u] at ht
    exact False.elim (hv1 (mul_left_cancel (ht.trans (mul_one u).symm)))
  · subst x
    rw [h.s_v] at hs
    exact False.elim (hu1 (mul_right_cancel (hs.trans (one_mul v).symm)))
  · subst x
    rw [map_mul, h.t_u, h.t_v] at ht
    have hh : u * v = u := mul_right_cancel ht
    exact False.elim (hv1 (mul_left_cancel (hh.trans (mul_one u).symm)))

end EightConfig
end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections
