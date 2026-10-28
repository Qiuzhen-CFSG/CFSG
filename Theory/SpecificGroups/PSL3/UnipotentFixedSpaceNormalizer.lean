module

public import Theory.SpecificGroups.PSL3.RootPlaneGeometry

/-!
# Normalizers of arbitrary nontrivial upper-unitriangular subgroups

For a subgroup `Q` of UT₃(F), its common fixed space consists of the vectors
satisfying `a * v₁ + c * v₂ = 0` and `b * v₂ = 0` for every matrix of `Q`.
It contains the first coordinate axis and, when `Q ≠ ⊥`, is proper. The
normalizer preserves this space. If there is a fixed vector outside the axis,
the equations identify the fixed space as a plane; otherwise it is the axis.

The plane is either already `v₂ = 0`, or has equation `v₁ = t * v₂`.
In the latter case the explicit matrix with lower block `!![0,1; -1,t]`
carries it to `v₂ = 0`. Its determinant is one, so the conjugation takes place
in SL₃ itself. Thus the full normalizer of every nontrivial subgroup of UT₃
is conjugate into an actual point or line parabolic. The argument works in
arbitrary characteristic.

This supplies the fixed-space input for the PSL₃ case of Aschbacher–Smith,
Theorem 0.1.2(1), printed p.4, repeated as Theorem 0.1.1(1) on printed p.482
of `refs/quasithin.pdf`. It does not assume a local-cover or classification
hypothesis.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree
namespace Matrix.PSL3.RootPlaneGeometry
variable (F : Type*) [Field F]

private def commonFixed (Q : Subgroup SL(3,F)) (v : Fin 3 → F) : Prop :=
  ∀ q ∈ Q, q • v = v

private theorem commonFixed_iff (Q : Subgroup SL(3,F)) (hQ : Q ≤ unipotentSL F)
    (v : Fin 3 → F) : commonFixed F Q v ↔
      ∀ q ∈ Q, q.val 0 1 * v 1 + q.val 0 2 * v 2 = 0 ∧
        q.val 1 2 * v 2 = 0 := by
  unfold commonFixed
  apply forall_congr'
  intro q
  apply forall_congr'
  intro hq
  change q.val.mulVec v = v ↔ _
  conv_lhs => rw [(mem_unipotentSL_iff F q).mp (hQ hq)]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [mulVec, dotProduct, Fin.sum_univ_three, -mul_eq_zero] at h0 h1
    exact ⟨by linear_combination h0, h1⟩
  · rintro ⟨h0,h1⟩
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three] at *
    · linear_combination h0
    · exact h1

private theorem commonFixed_normalizer (Q : Subgroup SL(3,F))
    (g : SL(3,F)) (hg : g ∈ Subgroup.normalizer Q)
    (v : Fin 3 → F) (hv : commonFixed F Q v) : commonFixed F Q (g • v) := by
  intro q hq
  have hc : g⁻¹ * q * g ∈ Q := (Subgroup.mem_normalizer_iff''.mp hg q).mp hq
  calc
    q • (g • v) = g • ((g⁻¹ * q * g) • v) := by simp [mul_smul]
    _ = g • v := by rw [hv _ hc]

private theorem commonFixed_axis (Q : Subgroup SL(3,F)) (hQ : Q ≤ unipotentSL F)
    (v : Fin 3 → F) (hv : v 1 = 0 ∧ v 2 = 0) : commonFixed F Q v := by
  rw [commonFixed_iff F Q hQ]
  intro q hq
  simp [hv.1,hv.2]

variable [Finite F]

private theorem normalizer_le_point (Q : Subgroup SL(3,F))
    (hQ : Q ≤ unipotentSL F)
    (hfix : ∀ v, commonFixed F Q v → v 1 = 0 ∧ v 2 = 0) :
    Subgroup.normalizer Q ≤ pointParabolicSL F := by
  intro g hg
  have h := hfix _ (commonFixed_normalizer F Q g hg _
    (commonFixed_axis F Q hQ ![1,0,0] (by simp)))
  exact (mem_pointParabolicSL_iff F g).mpr
    (by simpa [SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_three] using h)

private theorem normalizer_map_le_line (Q : Subgroup SL(3,F)) (s : SL(3,F))
    (hfix : ∀ v, commonFixed F Q v ↔ (s • v) 2 = 0) :
    (Subgroup.normalizer Q).map (MulAut.conj s).toMonoidHom ≤ lineParabolicSL F := by
  rintro _ ⟨g,hg,rfl⟩
  rw [lineParabolicSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
  intro v hv
  change ((s * g * s⁻¹) • v) 2 = 0
  have hf : commonFixed F Q (s⁻¹ • v) := (hfix _).mpr (by simpa using hv)
  have h := (hfix _).mp (commonFixed_normalizer F Q g hg _ hf)
  simpa only [mul_smul] using h

private def planeChange (t : F) : SL(3,F) :=
  ⟨!![1,0,0; 0,0,1; 0,-1,t], by simp [Matrix.det_fin_three]⟩

omit [Finite F] in
private theorem planeChange_apply (t : F) (v : Fin 3 → F) :
    (planeChange F t • v) 2 = -v 1 + t * v 2 := by
  change ((planeChange F t).val.mulVec v) 2 = _
  simp [planeChange, mulVec, dotProduct, Fin.sum_univ_three]

omit [Finite F] in
private theorem unipotent_eq_one (q : SL(3,F)) (hq : q ∈ unipotentSL F)
    (ha : q.val 0 1 = 0) (hc : q.val 0 2 = 0) (hb : q.val 1 2 = 0) : q = 1 := by
  apply Subtype.ext
  rw [(mem_unipotentSL_iff F q).mp hq, ha, hb, hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The full normalizer of any nontrivial subgroup of UT₃ is conjugate into
one of the two geometric parabolics; `true` denotes the point parabolic. -/
theorem normalizer_unipotent_subgroup_conjugate_le (Q : Subgroup SL(3,F))
    (hne : Q ≠ ⊥) (hQ : Q ≤ unipotentSL F) :
    ∃ (s : SL(3,F)) (point : Bool),
      (Subgroup.normalizer Q).map (MulAut.conj s).toMonoidHom ≤ parabolicSL F point := by
  classical
  by_cases hp : ∀ v, commonFixed F Q v → v 1 = 0 ∧ v 2 = 0
  · refine ⟨1, true, ?_⟩
    rintro _ ⟨g,hg,rfl⟩
    simpa [parabolicSL, MulAut.conj_apply] using normalizer_le_point F Q hQ hp hg
  push Not at hp
  obtain ⟨v,hv,hvnot⟩ := hp
  have hvcoords := (commonFixed_iff F Q hQ v).mp hv
  obtain ⟨q,hq,hqne⟩ := Q.bot_or_exists_ne_one.resolve_left hne
  by_cases hv2 : v 2 = 0
  · have hv1 : v 1 ≠ 0 := by simpa [hv2] using hvnot
    have ha (r : SL(3,F)) (hr : r ∈ Q) : r.val 0 1 = 0 := by
      have h := (hvcoords r hr).1
      rw [hv2, mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hv1
    have hfix (w : Fin 3 → F) : commonFixed F Q w ↔ w 2 = 0 := by
      constructor
      · intro hw
        by_contra hw2
        have hwcoords := (commonFixed_iff F Q hQ w).mp hw q hq
        have hc : q.val 0 2 = 0 := by
          have h := hwcoords.1
          rw [ha q hq, zero_mul, zero_add] at h
          exact (mul_eq_zero.mp h).resolve_right hw2
        have hb : q.val 1 2 = 0 := (mul_eq_zero.mp hwcoords.2).resolve_right hw2
        exact hqne (unipotent_eq_one F q (hQ hq) (ha q hq) hc hb)
      · intro hw
        rw [commonFixed_iff F Q hQ]
        intro r hr
        simp [ha r hr, hw]
    refine ⟨1, false, normalizer_map_le_line F Q 1 ?_⟩
    intro w
    simpa using hfix w
  · let t : F := v 1 / v 2
    have hb (r : SL(3,F)) (hr : r ∈ Q) : r.val 1 2 = 0 :=
      (mul_eq_zero.mp (hvcoords r hr).2).resolve_right hv2
    have hrel (r : SL(3,F)) (hr : r ∈ Q) : r.val 0 1 * t + r.val 0 2 = 0 := by
      apply (mul_eq_zero.mp (show (r.val 0 1 * t + r.val 0 2) * v 2 = 0 from ?_)).resolve_right hv2
      calc
        (r.val 0 1 * t + r.val 0 2) * v 2 =
            r.val 0 1 * v 1 + r.val 0 2 * v 2 := by
          simp [add_mul, mul_assoc, t, div_mul_cancel₀ _ hv2]
        _ = 0 := (hvcoords r hr).1
    have hqa : q.val 0 1 ≠ 0 := by
      intro ha
      have hc : q.val 0 2 = 0 := by simpa [ha] using hrel q hq
      exact hqne (unipotent_eq_one F q (hQ hq) ha hc (hb q hq))
    refine ⟨planeChange F t, false, normalizer_map_le_line F Q (planeChange F t) ?_⟩
    intro w
    rw [planeChange_apply]
    constructor
    · intro hw
      have he := ((commonFixed_iff F Q hQ w).mp hw q hq).1
      have hz : q.val 0 1 * (-w 1 + t * w 2) = 0 := by
        linear_combination (hrel q hq) * w 2 - he
      exact (mul_eq_zero.mp hz).resolve_left hqa
    · intro hw
      rw [commonFixed_iff F Q hQ]
      intro r hr
      constructor
      · linear_combination (hrel r hr) * w 2 - r.val 0 1 * hw
      · simp [hb r hr]

end Matrix.PSL3.RootPlaneGeometry
