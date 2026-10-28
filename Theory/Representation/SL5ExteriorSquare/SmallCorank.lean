module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry
public import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField

/-!
# Elements with small corank on the binary exterior square

An element of SL₅(2) fixing at least seven dimensions of Λ²(F₂⁵) has
square one. Its fixed space meets each conjugate of the four-space
v∧F₂⁵ nontrivially. The support of such a fixed decomposable bivector
is an invariant plane containing v. On a binary plane, an invertible
operator satisfies at v either A²v=v or A²v=v+Av. A vector space cannot
be the union of two proper kernels, so one polynomial holds everywhere.
The second polynomial is impossible in odd dimension, by taking traces.

This structural calculation supplies the full-automizer input to
Aschbacher--Smith, Lemma 12.5.6, printed pp.819--820. It uses the actual
exterior-square representation and does not enumerate the matrix group.
-/

public noncomputable section

open Subgroup
open scoped Matrix
namespace Representation.SL5ExteriorSquare.SmallActors
open SL5TenDimensional

private theorem binary_quadratic_at {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (e : W ≃ₗ[ZMod 2] W) (hd : Module.finrank (ZMod 2) W ≤ 2) (v : W) :
    e (e v) = v ∨ e (e v) = v + e v := by
  by_cases he : e v = v
  · exact Or.inl (by rw [he, he])
  have hv : v ≠ 0 := fun hh => he (by rw [hh, map_zero])
  have hev : e v ≠ 0 := fun hh => hv (e.injective (hh.trans (map_zero e).symm))
  have hi : LinearIndependent (ZMod 2) ![v, e v] := by
    apply (LinearIndependent.pair_iff' hv).mpr
    intro a
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · simpa only [zero_smul] using Ne.symm hev
    · simpa only [one_smul] using Ne.symm he
  let P := Submodule.span (ZMod 2) (Set.range ![v, e v])
  have hP : P = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hdim := finrank_span_eq_card hi
    change Module.finrank (ZMod 2) P = 2 at hdim
    have hle := Submodule.finrank_le P
    omega
  have hm : e (e v) ∈ Submodule.span (ZMod 2) {v, e v} := by
    have hh : e (e v) ∈ P := hP ▸ Submodule.mem_top
    have hr : Set.range ![v, e v] = ({v, e v} : Set W) := by ext; simp [or_comm]
    simpa only [P, hr] using hh
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp hm
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl <;>
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl <;>
    simp only [zero_smul, one_smul, zero_add, add_zero] at hab
  · exact (hev (e.injective (hab.symm.trans (map_zero e).symm))).elim
  · exact (he (e.injective hab).symm).elim
  · exact Or.inl hab.symm
  · exact Or.inr hab.symm

private theorem support_rank_le_two (w : V) (hw : w ∈ V₄) :
    Module.finrank (ZMod 2) (LinearMap.range (bivectorMatrix w).mulVecLin) ≤ 2 := by
  let z : Fin 5 → ZMod 2 := ![0,coordinates w 0,coordinates w 1,coordinates w 2,coordinates w 3]
  let u : Fin 5 → ZMod 2 := Pi.single 0 1
  have hc := (mem_coordinateSpan {0,1,2,3} w).mp hw
  have hspan : LinearMap.range (bivectorMatrix w).mulVecLin ≤
      Submodule.span (ZMod 2) (Set.range ![u,z]) := by
    rintro x ⟨y,rfl⟩
    have he : (bivectorMatrix w).mulVec y =
        ((bivectorMatrix w).mulVec y 0) • u + y 0 • z := by
      ext i
      fin_cases i <;>
        simp [bivectorMatrix, alternatingMatrix, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, u, z, hc 4 (by decide), hc 5 (by decide),
          hc 6 (by decide), hc 7 (by decide), hc 8 (by decide), hc 9 (by decide)]
        <;> ring
    change (bivectorMatrix w).mulVec y ∈ _
    rw [he]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1,rfl⟩)
  exact (Submodule.finrank_mono hspan).trans (finrank_range_le_card ![u,z])

private theorem quadratic_at_first (g : Group)
    (hd : 7 ≤ Module.finrank (ZMod 2) (fixedSpace g)) :
    specialLinearNatural 5 g (specialLinearNatural 5 g (Pi.single 0 1)) = Pi.single 0 1 ∨
      specialLinearNatural 5 g (specialLinearNatural 5 g (Pi.single 0 1)) =
        Pi.single 0 1 + specialLinearNatural 5 g (Pi.single 0 1) := by
  have hne : fixedSpace g ⊓ V₄ ≠ ⊥ := by
    intro hz
    have hs := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace g) V₄
    have hle := Submodule.finrank_le (fixedSpace g ⊔ V₄)
    rw [hz, finrank_bot] at hs
    rw [finrank_exteriorModule_two] at hle
    have hv := standard_dimensions.2.2.1
    omega
  obtain ⟨w, hw, hn⟩ := (Submodule.ne_bot_iff _).mp hne
  let P := LinearMap.range (bivectorMatrix w).mulVecLin
  let e := Matrix.SpecialLinearGroup.toLin' g
  have hP : P.map e.toLinearMap = P := by
    change P.map (specialLinearNatural 5 g) = P
    rw [← range_bivectorMatrix_action, (mem_fixedSpace g w).mp hw.1]
  let f : P ≃ₗ[ZMod 2] P := e.ofSubmodules P P hP
  let v : P := ⟨Pi.single 0 1, first_vector_mem_support_V₄ w hw.2 hn⟩
  have h := binary_quadratic_at f (support_rank_le_two w hw.2) v
  exact h.imp (congrArg Subtype.val) (congrArg Subtype.val)

private theorem exists_first_vector_map (v : Fin 5 → ZMod 2) (hv : v ≠ 0) :
    ∃ k : Group, specialLinearNatural 5 k (Pi.single 0 1) = v := by
  let u : Fin 5 → ZMod 2 := Pi.single 0 1
  let s : Fin 1 → (Fin 5 → ZMod 2) := fun _ => u
  let t : Fin 1 → (Fin 5 → ZMod 2) := fun _ => v
  have hs : LinearIndependent (ZMod 2) s := linearIndependent_unique_iff.mpr (by
    intro hz
    have hh := congrFun hz 0
    simp [s, u] at hh)
  have ht : LinearIndependent (ZMod 2) t := linearIndependent_unique_iff.mpr hv
  let e : Submodule.span (ZMod 2) (Set.range s) ≃ₗ[ZMod 2]
      Submodule.span (ZMod 2) (Set.range t) :=
    (Module.Basis.span hs).equiv (Module.Basis.span ht) (_root_.Equiv.refl (Fin 1))
  obtain ⟨f, hf⟩ := Submodule.exists_linearEquiv_restrict_eq e
  have hd : (LinearMap.toMatrix' f.toLinearMap).det = 1 := by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ f.isUnit_det'.ne_zero
  refine ⟨⟨LinearMap.toMatrix' f.toLinearMap, hd⟩, ?_⟩
  change (LinearMap.toMatrix' f.toLinearMap).mulVec u = v
  rw [LinearMap.toMatrix'_mulVec]
  change f u = v
  have hh := hf (Module.Basis.span hs 0)
  simpa only [e, Module.Basis.equiv_apply, _root_.Equiv.refl_apply,
    Module.Basis.coe_span_apply, s, t] using hh.symm

private theorem quadratic_at (g : Group)
    (hd : 7 ≤ Module.finrank (ZMod 2) (fixedSpace g)) (v : Fin 5 → ZMod 2) :
    specialLinearNatural 5 g (specialLinearNatural 5 g v) = v ∨
      specialLinearNatural 5 g (specialLinearNatural 5 g v) =
        v + specialLinearNatural 5 g v := by
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨k,hk⟩ := exists_first_vector_map v hv
  let a := k⁻¹ * g * k
  have hd' : 7 ≤ Module.finrank (ZMod 2) (fixedSpace a) := by
    have hr := finrank_displacement_conj k⁻¹ g
    rw [inv_inv] at hr
    have hn := LinearMap.finrank_range_add_finrank_ker (displacement g)
    have hn' := LinearMap.finrank_range_add_finrank_ker (displacement a)
    change Module.finrank (ZMod 2) (LinearMap.range (displacement g)) +
      Module.finrank (ZMod 2) (fixedSpace g) = _ at hn
    change Module.finrank (ZMod 2) (LinearMap.range (displacement a)) +
      Module.finrank (ZMod 2) (fixedSpace a) = _ at hn'
    change Module.finrank (ZMod 2) (LinearMap.range (displacement a)) = _ at hr
    omega
  have he (x : Fin 5 → ZMod 2) :
      specialLinearNatural 5 k (specialLinearNatural 5 a x) =
        specialLinearNatural 5 g (specialLinearNatural 5 k x) := by
    have hka : k * a = g * k := by dsimp only [a]; group
    have hh := congrArg (fun z => specialLinearNatural 5 z x) hka
    simpa only [map_mul, Module.End.mul_apply] using hh
  rcases quadratic_at_first a hd' with hh | hh
  · left
    have h := congrArg (specialLinearNatural 5 k) hh
    simpa only [he, hk] using h
  · right
    have h := congrArg (specialLinearNatural 5 k) hh
    simpa only [map_add, he, hk] using h

private theorem linear_disjunction {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f k : W →ₗ[ZMod 2] W) (h : ∀ v, f v = 0 ∨ k v = 0) : f = 0 ∨ k = 0 := by
  by_cases hf : f = 0
  · exact Or.inl hf
  right
  have hex : ∃ v, f v ≠ 0 := by
    by_contra! hh
    exact hf (LinearMap.ext hh)
  obtain ⟨v,hv⟩ := hex
  have hkv := (h v).resolve_left hv
  apply LinearMap.ext
  intro w
  by_cases hw : f w = 0
  · have hfv : f (v+w) ≠ 0 := by simpa only [map_add,hw,add_zero] using hv
    have hk := (h (v+w)).resolve_left hfv
    simpa only [map_add,hkv,zero_add, LinearMap.zero_apply] using hk
  · exact (h w).resolve_left hw

/-- A seven-dimensional fixed space forces square one in the natural group. -/
theorem square_eq_one_of_large_fixedSpace (g : Group)
    (hd : 7 ≤ Module.finrank (ZMod 2) (fixedSpace g)) : g * g = 1 := by
  let A := specialLinearNatural 5 g
  have hsplit : A * A - 1 = 0 ∨ A * A - 1 - A = 0 :=
    linear_disjunction (A*A-1) (A*A-1-A) (fun v => by
      rcases quadratic_at g hd v with hv | hv
      · left
        change A (A v) - v = 0
        exact sub_eq_zero.mpr hv
      · right
        change A (A v) - v - A v = 0
        rw [hv]
        abel)
  rcases hsplit with hsq | hcub
  · have hA : specialLinearNatural 5 (g*g) = specialLinearNatural 5 1 := by
      rw [map_mul,map_one]
      exact sub_eq_zero.mp hsq
    apply Matrix.SpecialLinearGroup.toLin'_injective
    exact LinearEquiv.toLinearMap_injective hA
  · have hA : A * A = 1 + A := by
      have hh := sub_eq_zero.mp hcub
      exact (sub_eq_iff_eq_add.mp hh).trans (add_comm A 1)
    have hm : g.val ^ 2 = 1 + g.val := by
      ext i j
      have hh := congrArg (fun f : Module.End (ZMod 2) (Fin 5 → ZMod 2) =>
        f (Pi.single j 1) i) hA
      change g.val.mulVec (g.val.mulVec (Pi.single j 1)) i =
        (Pi.single j (1 : ZMod 2) : Fin 5 → ZMod 2) i + g.val.mulVec (Pi.single j 1) i at hh
      rw [Matrix.mulVec_mulVec] at hh
      simpa only [pow_two, Matrix.mulVec_single_one,
        Matrix.add_apply, Matrix.col_apply, Matrix.one_apply, Pi.single_apply] using hh
    have ht := congrArg Matrix.trace hm
    rw [ZMod.trace_pow_card, Matrix.trace_add, Matrix.trace_one] at ht
    have ht2 : (Matrix.trace g.val)^2 = Matrix.trace g.val := by
      exact (by decide : ∀ a : ZMod 2, a^2 = a) _
    rw [ht2] at ht
    have hc : (Fintype.card (Fin 5) : ZMod 2) = 1 := by decide
    rw [hc] at ht
    have hh : (1 : ZMod 2) = 0 := by linear_combination -ht
    exact (one_ne_zero hh).elim

end Representation.SL5ExteriorSquare.SmallActors
