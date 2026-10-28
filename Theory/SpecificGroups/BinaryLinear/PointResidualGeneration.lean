module

public import Theory.SpecificGroups.BinaryLinear.CubicPairNormalizers.CoreAbsorption.Elementary
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.ConjugateSpanSylow
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# Generation by a binary point residual

Let A be a line in a finite binary vector space of dimension at least three,
and let B strictly contain A. The conjugates of O²(GL(E)_A) under GL(E)_B
generate GL(E). Choose basis vectors a on A and b in B outside A. The point
residual contains every shear toward a and every cubic element supported on
two other coordinates. Commuting with the shear from a to b recovers all
elementary matrices, including in dimension three. Gaussian elimination
then gives the whole linear group. An adapted basis transports the actual
stabilizers and their intrinsic two-residuals to arbitrary A and B.

This proves the linear calculation in Aschbacher–Smith, combined manuscript
of 1 March 2004, Lemma 12.8.5(2), printed p.850 (PDF p.867). No perfectness
of the point stabilizer is required.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace BinaryLinear.PointResidualGeneration
open OuterCyclic CubicPairNormalizers.CoreAbsorption

private theorem root_commutator {n : ℕ} (r k s : Fin n)
    (hrk : r ≠ k) (hrs : r ≠ s) (hks : k ≠ s) :
    ⁅root r k hrk 1, root k s hks 1⁆ = root r s hrs 1 := by
  ext v t
  simp only [commutatorElement_def, root_inv, LinearEquiv.mul_apply, root_apply, mul_one]
  by_cases htr : t = r <;> by_cases htk : t = k <;>
    simp [htr, htk, hrk, hrk.symm, hrs.symm, hks.symm] <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      mul_one, mul_zero, add_zero]

private theorem eq_top_of_roots {n : ℕ} (hn : 3 ≤ n) (H : Subgroup (LinearGroup n))
    (hH : ∀ r s (hrs : r ≠ s), root r s hrs 1 ∈ H) : H = ⊤ := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  apply top_unique
  intro g _
  obtain ⟨g, rfl⟩ := (slEquivLinear n).surjective g
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
    (fun x => slEquivLinear n x ∈ H) g ?_ ?_ ?_
  · intro i j hij c hc
    have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc
    have hd : Matrix.SpecialLinearGroup.diag2n hij c hc = 1 := by
      apply Subtype.ext
      simp [Matrix.SpecialLinearGroup.diag2n_coe, hc1]
    rw [hd, map_one]
    exact H.one_mem
  · intro i j hij c
    have he : slEquivLinear n (Matrix.SpecialLinearGroup.transvection hij c) =
        root i j hij c := by
      ext v k
      rw [slEquivLinear_apply]
      simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
        Matrix.single_mulVec_eq, root_apply, Pi.single_apply, mul_comm]
    rw [he]
    by_cases hc : c = 0
    · simp [hc]
    · rw [(by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc]
      exact hH i j hij
  · intro x y hx hy
    simpa only [map_mul] using H.mul_mem hx hy

private theorem root_mem_point {n : ℕ} (a r s : Fin n) (hrs : r ≠ s)
    (hsa : s ≠ a) :
    root r s hrs 1 ∈ parabolic (Submodule.span (ZMod 2) {Pi.single a 1}) := by
  have hfix : root r s hrs 1 (Pi.single a 1) = Pi.single a 1 := by
    ext k
    simp [root_apply, Pi.single_apply, hsa]
  have hpres (v : Space n) (hv : v ∈ Submodule.span (ZMod 2) {Pi.single a 1}) :
      root r s hrs 1 v ∈ Submodule.span (ZMod 2) {Pi.single a 1} := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hfix]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  intro v
  refine ⟨fun hv => ?_, hpres v⟩
  have hh := hpres (root r s hrs 1 v) hv
  change (root r s hrs 1)⁻¹ (root r s hrs 1 v) ∈ _ at hh
  simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using hh

private theorem root_mem_point_residual {n : ℕ} (hn : 3 ≤ n) (a s : Fin n)
    (has : a ≠ s) : root a s has 1 ∈
      (pResidual 2 (parabolic (Submodule.span (ZMod 2) {Pi.single a 1}))).map
        (parabolic (Submodule.span (ZMod 2) {Pi.single a 1})).subtype := by
  classical
  let c : Fin n → ℕ := fun j => if j = a then 0 else 1
  apply root_mem_residual c _ ?_ a s has ?_ ?_
  · intro r s hrs hle
    apply root_mem_point a r s hrs
    intro hsa
    subst s
    simp [c, hrs] at hle
  · simp [c, has.symm]
  · obtain ⟨k, hka, hks⟩ := Fin.exists_ne_and_ne_of_two_lt a s (by omega)
    exact Or.inr ⟨k, hks, by simp [c, hka, has.symm]⟩

private theorem cubic_mem_point_residual {n : ℕ} (a r s : Fin n)
    (hrs : r ≠ s) (hra : r ≠ a) (hsa : s ≠ a) : cubic r s hrs ∈
      (pResidual 2 (parabolic (Submodule.span (ZMod 2) {Pi.single a 1}))).map
        (parabolic (Submodule.span (ZMod 2) {Pi.single a 1})).subtype := by
  let P : Subgroup (LinearGroup n) := parabolic (Submodule.span (ZMod 2) {Pi.single a 1})
  let x : P := ⟨cubic r s hrs, P.mul_mem
    (root_mem_point a r s hrs hsa) (root_mem_point a s r hrs.symm hra)⟩
  refine mem_map.mpr ⟨x, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  exact (by decide : Nat.Coprime 2 3).of_dvd_right
    (orderOf_dvd_of_pow_eq_one (show x ^ 3 = 1 from Subtype.ext (cubic_cube r s hrs)))

private theorem comm_mem_right {K : Type*} [Group K] (H : Subgroup K)
    {x y : K} (hx : x ∈ normalizer (H : Set K)) (hy : y ∈ H) : ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem ((mem_normalizer_iff.mp hx y).mp hy) (H.inv_mem hy)

private theorem comm_mem_left {K : Type*} [Group K] (H : Subgroup K)
    {x y : K} (hx : x ∈ H) (hy : y ∈ normalizer (H : Set K)) : ⁅x, y⁆ ∈ H := by
  have h := H.inv_mem (comm_mem_right H hy hx)
  simpa only [commutatorElement_inv] using h

/-- A single shear moving the marked point normally generates GL from its
point two-residual. The cubic tail elements handle dimension three. -/
private theorem coordinate_generation {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) (hab : a ≠ b)
    (H : Subgroup (LinearGroup n))
    (hR : (pResidual 2 (parabolic (Submodule.span (ZMod 2) {Pi.single a 1}))).map
      (parabolic (Submodule.span (ZMod 2) {Pi.single a 1})).subtype ≤ H)
    (ht : root b a hab.symm 1 ∈ normalizer (H : Set (LinearGroup n))) : H = ⊤ := by
  have hrow (j : Fin n) (haj : a ≠ j) : root a j haj 1 ∈ H :=
    hR (root_mem_point_residual hn a j haj)
  have hbj (j : Fin n) (hja : j ≠ a) (hjb : j ≠ b) : root b j hjb.symm 1 ∈ H := by
    rw [← root_commutator b a j hab.symm hjb.symm hja.symm]
    exact comm_mem_right H ht (hrow j hja.symm)
  have hjb (j : Fin n) (hja : j ≠ a) (hjb : j ≠ b) : root j b hjb 1 ∈ H := by
    have hc := hR (cubic_mem_point_residual a b j hjb.symm hab.symm hja)
    have hm := H.mul_mem (H.inv_mem (hbj j hja hjb)) hc
    simpa only [cubic, inv_mul_cancel_left] using hm
  have hja (j : Fin n) (hja : j ≠ a) (hjb' : j ≠ b) : root j a hja 1 ∈ H := by
    rw [← root_commutator j b a hjb' hja hab.symm]
    exact comm_mem_left H (hjb j hja hjb') ht
  obtain ⟨c, hca, hcb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
  have hba : root b a hab.symm 1 ∈ H := by
    rw [← root_commutator b c a hcb.symm hab.symm hca]
    exact comm_mem_right H (H.le_normalizer (hbj c hca hcb)) (hja c hca hcb)
  apply eq_top_of_roots hn H
  intro r s hrs
  by_cases hra : r = a
  · subst r
    exact hrow s hrs
  by_cases hsa : s = a
  · subst s
    by_cases hrb : r = b
    · subst r
      exact hba
    · exact hja r hra hrb
  by_cases hrb : r = b
  · subst r
    exact hbj s hsa hrs.symm
  by_cases hsb : s = b
  · subst s
    exact hjb r hra hrs
  rw [← root_commutator r b s hrb hrs (Ne.symm hsb)]
  exact comm_mem_right H (H.le_normalizer (hjb r hra hrb)) (hbj s hsa hsb)

private theorem root_mem_parabolic {n : ℕ} (B : Submodule (ZMod 2) (Space n))
    (r s : Fin n) (hrs : r ≠ s) (hr : Pi.single r 1 ∈ B) :
    root r s hrs 1 ∈ parabolic B := by
  have hp (v : Space n) (hv : v ∈ B) : root r s hrs 1 v ∈ B := by
    change v + v s • Pi.single r 1 ∈ B
    exact B.add_mem hv (B.smul_mem _ hr)
  intro v
  refine ⟨fun hv => ?_, hp v⟩
  have hh := hp (root r s hrs 1 v) hv
  change (root r s hrs 1)⁻¹ (root r s hrs 1 v) ∈ B at hh
  simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using hh

private theorem coordinate_span {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) (hab : a ≠ b)
    (B : Submodule (ZMod 2) (Space n)) (hb : Pi.single b 1 ∈ B) :
    conjugateSpanBy
      ((pResidual 2 (parabolic (Submodule.span (ZMod 2) {Pi.single a 1}))).map
        (parabolic (Submodule.span (ZMod 2) {Pi.single a 1})).subtype)
      (parabolic B) = ⊤ :=
  coordinate_generation hn a b hab _ (le_conjugateSpanBy _ _)
    (le_normalizer_conjugateSpanBy _ _ (root_mem_parabolic B b a hab.symm hb))

open SmallParabolicLevi
variable {E U : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup U] [Module (ZMod 2) U]

private theorem map_parabolic (e : U ≃ₗ[ZMod 2] E) (W : Submodule (ZMod 2) U) :
    (parabolic W).map (linearGroupCongr e).toMonoidHom =
      parabolic (W.map e.toLinearMap) := by
  ext g
  obtain ⟨g, rfl⟩ := (linearGroupCongr e).surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  change (∀ v, g v ∈ W ↔ v ∈ W) ↔
    ∀ w, linearGroupCongr e g w ∈ W.map e.toLinearMap ↔ w ∈ W.map e.toLinearMap
  simp only [Submodule.mem_map_equiv, linearGroupCongr_apply,
    LinearEquiv.symm_apply_apply]
  constructor
  · intro hg w
    exact hg (e.symm w)
  · intro hg v
    simpa only [LinearEquiv.symm_apply_apply] using hg (e v)

private theorem adapted_coordinates [FiniteDimensional (ZMod 2) E]
    (A B : Submodule (ZMod 2) E) (hA : Module.finrank (ZMod 2) A = 1)
    (hAB : A < B) :
    ∃ (m : ℕ) (e : Space m ≃ₗ[ZMod 2] E) (a b : Fin m), a ≠ b ∧
      Module.finrank (ZMod 2) E = m ∧
      (Submodule.span (ZMod 2) {Pi.single a 1}).map e.toLinearMap = A ∧
      e (Pi.single b 1) ∈ B := by
  classical
  let : Finite E := Module.finite_of_finite (ZMod 2)
  have hA0 : A ≠ ⊥ := by
    intro he
    have hz := Submodule.finrank_eq_zero.mpr he
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0
  obtain ⟨y, hyB, hyA⟩ := SetLike.exists_of_lt hAB
  have hs : A = Submodule.span (ZMod 2) {x} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hA hx hx0
  have hlin : LinearIndependent (ZMod 2) ![y, x] := by
    rw [linearIndependent_fin2]
    refine ⟨hx0, ?_⟩
    intro c he
    change c • x = y at he
    exact hyA (he ▸ A.smul_mem c hx)
  let h := hlin.linearIndepOn_id
  let I := h.extend (Set.subset_univ _)
  let d : Module.Basis I (ZMod 2) E := Module.Basis.extend h
  let ia : I := ⟨x, h.subset_extend (Set.subset_univ _) ⟨1, rfl⟩⟩
  let ib : I := ⟨y, h.subset_extend (Set.subset_univ _) ⟨0, rfl⟩⟩
  let : Fintype I := Fintype.ofFinite I
  let m := Fintype.card I
  let q : I ≃ Fin m := Fintype.equivFin I
  let d' := d.reindex q
  let e : Space m ≃ₗ[ZMod 2] E := d'.equivFun.symm
  have he (i : I) : e (Pi.single (q i) 1) = (i : E) := by
    change d'.equivFun.symm (Pi.single (q i) 1) = (i : E)
    rw [Module.Basis.equivFun_symm_apply]
    simp [d', d]
    exact Module.Basis.extend_apply_self h i
  refine ⟨m, e, q ia, q ib, ?_, Module.finrank_eq_card_basis d, ?_, ?_⟩
  · intro hab
    have hxy : x = y := congrArg Subtype.val (q.injective hab)
    exact hyA (hxy ▸ hx)
  · rw [Submodule.map_span, Set.image_singleton]
    change Submodule.span (ZMod 2) {e (Pi.single (q ia) 1)} = A
    rw [he]
    exact hs.symm
  · simpa only [he] using hyB

/-- In binary dimension at least three, the two-residual of a point stabilizer
and its conjugates under any larger subspace stabilizer generate all of GL. -/
theorem conjugateSpanBy_point_residual_eq_top [FiniteDimensional (ZMod 2) E]
    (A B : Submodule (ZMod 2) E) (hE : 3 ≤ Module.finrank (ZMod 2) E)
    (hA : Module.finrank (ZMod 2) A = 1) (hAB : A < B) :
    conjugateSpanBy ((pResidual 2 (parabolic A)).map (parabolic A).subtype)
      (parabolic B) = ⊤ := by
  let : Finite E := Module.finite_of_finite (ZMod 2)
  obtain ⟨m, e, a, b, hab, hm, hAe, hb⟩ := adapted_coordinates A B hA hAB
  let : Finite (LinearGroup m) := Finite.of_injective
    (fun g : LinearGroup m => (g : Space m → Space m)) DFunLike.coe_injective
  let B₀ := B.comap e.toLinearMap
  have hB : B₀.map e.toLinearMap = B := Submodule.map_comap_eq_of_surjective e.surjective B
  have h := congrArg (Subgroup.map (linearGroupCongr e).toMonoidHom)
    (coordinate_span (by omega : 3 ≤ m) a b hab B₀ hb)
  rw [map_conjugateSpanBy, map_embedded_pResidual, map_parabolic, hAe,
    map_parabolic, hB, Subgroup.map_top_of_surjective _ (linearGroupCongr e).surjective] at h
  exact h

end BinaryLinear.PointResidualGeneration
