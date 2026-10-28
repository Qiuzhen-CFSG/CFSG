module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.VectorNormalForm
import Mathlib.Tactic.Ring

/-!
# Simple binary bivectors and their stars

A nonzero simple wedge has support equal to the plane spanned by its factors.
The rank-two/rank-four normal forms identify these wedges with the actual
SL₅(2) orbit of the first exterior basis vector. Binary scalars make a support
plane determine its nonzero bivector uniquely. The range of x ↦ a ∧ x has
kernel ⟨a⟩ and dimension four; two distinct such stars intersect in ⟨a ∧ b⟩.

These are the exterior-geometric inputs to the Grassmann clique argument in
Meierfrankenfeld–Stellmacher (1993), (1.6), pp.845–847, applied to the literal
module in Aschbacher–Smith §12.5, pp.817–821.
-/

@[expose] public section

open scoped Matrix
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
namespace DecomposablePreserver

abbrev N := Fin 5 → ZMod 2

noncomputable def wedge (a b : N) : V :=
  exteriorPower.ιMulti (ZMod 2) 2 ![a,b]

theorem coordinates_wedge (a b : N) (s : Fin 10) :
    coordinates (wedge a b) s =
      a (pair s 0) * b (pair s 1) + b (pair s 0) * a (pair s 1) := by
  simp only [coordinates_apply, exteriorCoordinates, Module.Basis.equivFun_apply,
    exteriorBasis, exteriorPower.basis_repr_apply, wedge,
    exteriorPower.ιMultiDual_apply_ιMulti, Module.Basis.coord_apply,
    Pi.basisFun_repr, index_order, Matrix.det_fin_two]
  simp [pairEmbedding, sub_eq_add_neg, ZMod.neg_eq_self_mod_two, mul_comm]

theorem wedge_add_right (a b c : N) : wedge a (b+c) = wedge a b + wedge a c := by
  apply coordinates.injective
  ext s
  simp only [map_add, Pi.add_apply, coordinates_wedge]
  ring

theorem wedge_smul_right (r : ZMod 2) (a b : N) : wedge a (r • b) = r • wedge a b := by
  apply coordinates.injective
  ext s
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, coordinates_wedge]
  ring

theorem wedge_comm (a b : N) : wedge a b = wedge b a := by
  apply coordinates.injective
  ext s
  simp only [coordinates_wedge]
  ring

theorem wedge_self (a : N) : wedge a a = 0 := by
  apply coordinates.injective
  ext s
  simp only [coordinates_wedge, map_zero, Pi.zero_apply, ← two_mul,
    show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem wedge_action (g : Group) (a b : N) :
    exteriorAction 2 g (wedge a b) =
      wedge (specialLinearNatural 5 g a) (specialLinearNatural 5 g b) := by
  rw [wedge, exteriorAction_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem bivectorMatrix_wedge (a b : N) :
    bivectorMatrix (wedge a b) = Matrix.of (fun i j => a i * b j + b i * a j) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-coordinates_apply, bivectorMatrix, alternatingMatrix, coordinates_wedge, pair,
      mul_comm, ← two_mul, show (2 : ZMod 2) = 0 from rfl]
      <;> ring

theorem wedge_mulVec (a b x : N) :
    (bivectorMatrix (wedge a b)).mulVec x = (dotProduct b x) • a + (dotProduct a x) • b := by
  rw [bivectorMatrix_wedge]
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

noncomputable def support (v : V) : Submodule (ZMod 2) N :=
  LinearMap.range (bivectorMatrix v).mulVecLin

theorem finrank_support_of_decomposable {v : V} (h : InExteriorOrbit decomposable v) :
    Module.finrank (ZMod 2) (support v) = 2 := by
  obtain ⟨g, rfl⟩ := h
  exact (rank_bivectorMatrix_action g decomposable).trans rank_bivectorMatrix_decomposable

theorem finrank_support_of_nondecomposable {v : V} (h : InExteriorOrbit nondecomposable v) :
    Module.finrank (ZMod 2) (support v) = 4 := by
  obtain ⟨g, rfl⟩ := h
  exact (rank_bivectorMatrix_action g nondecomposable).trans rank_bivectorMatrix_nondecomposable

theorem bivectorMatrix_zero : bivectorMatrix 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bivectorMatrix, alternatingMatrix]

theorem support_zero : support 0 = ⊥ := by
  simp [support, bivectorMatrix_zero]

theorem decomposable_iff_finrank_support (v : V) :
    InExteriorOrbit decomposable v ↔ Module.finrank (ZMod 2) (support v) = 2 := by
  refine ⟨finrank_support_of_decomposable, ?_⟩
  intro h
  have hv : v ≠ 0 := by
    intro hv
    rw [hv, support_zero, finrank_bot] at h
    omega
  rcases exterior_orbits_exhaustive v hv with hd | hn
  · exact hd
  · have := finrank_support_of_nondecomposable hn
    omega

theorem support_wedge_le (a b : N) :
    support (wedge a b) ≤ Submodule.span (ZMod 2) {a,b} := by
  rintro x ⟨y,rfl⟩
  change (bivectorMatrix (wedge a b)).mulVec y ∈ _
  rw [wedge_mulVec]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem finrank_span_pair_le (a b : N) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {a,b}) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := ZMod 2) ({a,b} : Finset N)
  have hc : ({a,b} : Finset N).card ≤ 2 := by
    calc
      _ ≤ ({b} : Finset N).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  have hset : (↑({a,b} : Finset N) : Set N) = {a,b} := by ext; simp
  change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) _) ≤ _ at h
  rw [hset] at h
  exact h.trans hc

theorem wedge_mem_decomposable {a b : N} (h : wedge a b ≠ 0) :
    InExteriorOrbit decomposable (wedge a b) := by
  rcases exterior_orbits_exhaustive (wedge a b) h with hd | hn
  · exact hd
  · have hle := (Submodule.finrank_mono (support_wedge_le a b)).trans (finrank_span_pair_le a b)
    rw [finrank_support_of_nondecomposable hn] at hle
    omega

theorem support_wedge {a b : N} (h : wedge a b ≠ 0) :
    support (wedge a b) = Submodule.span (ZMod 2) {a,b} := by
  apply Submodule.eq_of_le_of_finrank_le (support_wedge_le a b)
  rw [finrank_support_of_decomposable (wedge_mem_decomposable h)]
  exact finrank_span_pair_le a b

theorem exists_wedge_of_decomposable {v : V} (h : InExteriorOrbit decomposable v) :
    ∃ a b : N, wedge a b = v := by
  obtain ⟨g,rfl⟩ := h
  refine ⟨specialLinearNatural 5 g (Pi.single 0 1),
    specialLinearNatural 5 g (Pi.single 1 1), ?_⟩
  rw [← wedge_action, decomposable, basis_wedge]
  congr 1

theorem decomposable_iff_wedge (v : V) :
    InExteriorOrbit decomposable v ↔ v ≠ 0 ∧ ∃ a b : N, wedge a b = v := by
  refine ⟨fun h => ⟨fun hv => decomposable_ne_zero (h.eq_zero_iff.mpr hv),
    exists_wedge_of_decomposable h⟩, ?_⟩
  rintro ⟨hv,a,b,rfl⟩
  exact wedge_mem_decomposable hv

theorem wedge_add_left (a b c : N) : wedge (a+b) c = wedge a c + wedge b c := by
  rw [wedge_comm, wedge_add_right, wedge_comm c a, wedge_comm c b]

theorem wedge_smul_left (r : ZMod 2) (a b : N) : wedge (r • a) b = r • wedge a b := by
  rw [wedge_comm, wedge_smul_right, wedge_comm b a]

@[simp] theorem wedge_zero_right (a : N) : wedge a 0 = 0 := by
  have h := wedge_smul_right 0 a a
  simpa only [zero_smul] using h

@[simp] theorem wedge_zero_left (a : N) : wedge 0 a = 0 := by
  rw [wedge_comm, wedge_zero_right]

theorem wedge_eq_zero_iff {a : N} (ha : a ≠ 0) (b : N) :
    wedge a b = 0 ↔ b ∈ Submodule.span (ZMod 2) {a} := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra! hn
      exact ha (funext hn)
    have hi1 : a i = 1 := (by decide : ∀ r : ZMod 2, r ≠ 0 → r = 1) _ hi
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b i, ?_⟩
    ext j
    have hh := congrArg (fun M => M i j) (congrArg bivectorMatrix h)
    rw [bivectorMatrix_wedge, bivectorMatrix_zero] at hh
    change a i * b j + b i * a j = 0 at hh
    rw [hi1, one_mul, add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two] at hh
    exact hh.symm
  · rintro hb
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [wedge_smul_right, wedge_self, smul_zero]

/-- A star is the range of the linear map x ↦ a ∧ x. -/
noncomputable def wedgeLeft (a : N) : N →ₗ[ZMod 2] V where
  toFun := wedge a
  map_add' := wedge_add_right a
  map_smul' r b := wedge_smul_right r a b

noncomputable def star (a : N) : Submodule (ZMod 2) V := LinearMap.range (wedgeLeft a)

theorem mem_star (a : N) (v : V) : v ∈ star a ↔ ∃ b : N, wedge a b = v := Iff.rfl

theorem ker_wedgeLeft {a : N} (ha : a ≠ 0) :
    LinearMap.ker (wedgeLeft a) = Submodule.span (ZMod 2) {a} := by
  ext b
  exact wedge_eq_zero_iff ha b

theorem finrank_star {a : N} (ha : a ≠ 0) : Module.finrank (ZMod 2) (star a) = 4 := by
  have h := (wedgeLeft a).finrank_range_add_finrank_ker
  rw [ker_wedgeLeft ha, finrank_span_singleton ha] at h
  have hN : Module.finrank (ZMod 2) N = 5 := by simp [N]
  rw [hN] at h
  change Module.finrank (ZMod 2) (LinearMap.range (wedgeLeft a)) = 4
  omega

theorem decomposable_of_mem_star {a : N} {v : V} (hv : v ∈ star a) (h0 : v ≠ 0) :
    InExteriorOrbit decomposable v := by
  obtain ⟨b,rfl⟩ := hv
  exact wedge_mem_decomposable h0

theorem wedge_linear_combination (a b : N) (r s t u : ZMod 2) :
    wedge (r • a + s • b) (t • a + u • b) = (r*u+s*t) • wedge a b := by
  simp only [wedge_add_left, wedge_add_right, wedge_smul_left, wedge_smul_right,
    wedge_self, smul_zero, zero_add, add_zero, wedge_comm b a, smul_smul, add_smul]
  simp only [mul_comm t s, mul_comm u r, add_comm]

theorem wedge_mem_binaryPoint_of_mem_span_pair {a b c d : N}
    (hc : c ∈ Submodule.span (ZMod 2) {a,b})
    (hd : d ∈ Submodule.span (ZMod 2) {a,b}) :
    wedge c d ∈ Submodule.span (ZMod 2) {wedge a b} := by
  obtain ⟨r,s,rfl⟩ := Submodule.mem_span_pair.mp hc
  obtain ⟨t,u,rfl⟩ := Submodule.mem_span_pair.mp hd
  rw [wedge_linear_combination]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- Over F₂ the support plane uniquely determines its nonzero bivector. -/
theorem eq_of_support_eq {v w : V} (hv : InExteriorOrbit decomposable v)
    (hw : InExteriorOrbit decomposable w) (h : support v = support w) : v = w := by
  obtain ⟨hv0,a,b,rfl⟩ := (decomposable_iff_wedge v).mp hv
  obtain ⟨hw0,c,d,rfl⟩ := (decomposable_iff_wedge w).mp hw
  rw [support_wedge hv0, support_wedge hw0] at h
  have hmem := wedge_mem_binaryPoint_of_mem_span_pair
    (a := c) (b := d) (c := a) (d := b)
    (h ▸ Submodule.subset_span (by simp)) (h ▸ Submodule.subset_span (by simp))
  exact ((mem_binaryPoint _ _).mp hmem).resolve_left hv0

theorem mem_star_iff_mem_support {a : N} (ha : a ≠ 0) {v : V}
    (hv : InExteriorOrbit decomposable v) : v ∈ star a ↔ a ∈ support v := by
  rw [mem_star]
  constructor
  · rintro ⟨b,rfl⟩
    rw [support_wedge (fun hz => decomposable_ne_zero (hv.eq_zero_iff.mpr hz))]
    exact Submodule.subset_span (by simp)
  · intro hm
    obtain ⟨hv0,b,c,rfl⟩ := (decomposable_iff_wedge v).mp hv
    rw [support_wedge hv0] at hm
    obtain ⟨r,s,he⟩ := Submodule.mem_span_pair.mp hm
    have hr : r = 0 ∨ r = 1 := (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r
    have hs : s = 0 ∨ s = 1 := (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) s
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at he
    · exact (ha he.symm).elim
    · exact ⟨b, by rw [← he, wedge_comm]⟩
    · exact ⟨c, by rw [← he]⟩
    · exact ⟨c, by rw [← he, wedge_add_left, wedge_self, add_zero]⟩

theorem wedge_ne_zero {a b : N} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    wedge a b ≠ 0 := by
  intro h
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp ((wedge_eq_zero_iff ha b).mp h)
  rcases (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r with rfl | rfl
  · exact hb (by simpa using hr.symm)
  · exact hab (by simpa using hr)

theorem star_intersection {a b : N} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    star a ⊓ star b = Submodule.span (ZMod 2) {wedge a b} := by
  have hw0 := wedge_ne_zero ha hb hab
  apply le_antisymm
  · intro v hv
    by_cases hv0 : v = 0
    · exact hv0 ▸ Submodule.zero_mem _
    have hd := decomposable_of_mem_star hv.1 hv0
    have hle : Submodule.span (ZMod 2) {a,b} ≤ support v := by
      apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact (mem_star_iff_mem_support ha hd).mp hv.1
      · have he : x = b := Set.mem_singleton_iff.mp hx
        exact he ▸ (mem_star_iff_mem_support hb hd).mp hv.2
    have he : support (wedge a b) = support v := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rwa [support_wedge hw0]
      · rw [finrank_support_of_decomposable (wedge_mem_decomposable hw0),
          finrank_support_of_decomposable hd]
    rw [eq_of_support_eq hd (wedge_mem_decomposable hw0) he.symm]
    exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    rintro v (rfl : v = wedge a b)
    exact ⟨(mem_star _ _).mpr ⟨b,rfl⟩,
      (mem_star _ _).mpr ⟨a,wedge_comm b a⟩⟩

theorem star_injective {a b : N} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : star a = star b) : a = b := by
  by_contra hab
  have hi := star_intersection ha hb hab
  rw [← h, inf_idem] at hi
  have hd := congrArg (fun S : Submodule (ZMod 2) V => Module.finrank (ZMod 2) S) hi
  rw [finrank_star ha, finrank_span_singleton (wedge_ne_zero ha hb hab)] at hd
  omega

end DecomposablePreserver
end Representation.SL5ExteriorSquare
