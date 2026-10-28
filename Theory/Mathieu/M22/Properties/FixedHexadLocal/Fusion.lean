module
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.Generators

/-!
# Involution fusion and fixed-hexad transport in M22

The M23 involution centralizer acts transitively on its seven fixed points:
a product of two certified generators supplies a seven-cycle for the standard
representative, and M23 fusion transports this action. Thus a conjugator
between two involutions fixing point 9 can be corrected by a centralizing
element to fix point 9 itself. The concrete point-stabilizer equivalence then
proves involution fusion in M22.

The fixed hexad and its pointwise kernel transform by the resulting actual
permutation conjugation. This permits intrinsic local calculations at one
representative to be transported to all involutions.

Source: Aschbacher--Smith, 1.1.5(3)(f) and 2.3.9(7)(f), printed pp.502 and
525--526; the M23 fusion and generator certificates are in the cited imports.
-/

public section
namespace Sporadic.Mathieu
open Subgroup M23Geometry
open scoped Pointwise

private theorem centralizer_transitive_fixed (t : M23) (ht : orderOf t = 2)
    (a b : Fin 23) (ha : t • a = a) (hb : t • b = b) :
    ∃ c : centralizer ({t} : Set M23), (c : M23) • a = b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (involutions_isConj involutionRepresentative t involutionRepresentative_order ht)
  have fix (x : Fin 23) (hx : t • x = x) : g⁻¹ • x ∈ involutionHeptad := by
    apply (involutionRepresentative_fixed_iff _).mp
    change involutionRepresentative • (g⁻¹ • x) = g⁻¹ • x
    have he := congrArg (fun y : Fin 23 => g⁻¹ • y) hx
    rw [← hg] at he
    simpa only [mul_smul, inv_smul_smul] using he
  let s := involutionCentralizerGenerator 6 * involutionCentralizerGenerator 4
  have hs : ∀ x y : Fin 23, x ∈ involutionHeptad → y ∈ involutionHeptad →
      ∃ n : Fin 7, ((s ^ n.val).val.val) x = y := by
    decide +kernel
  obtain ⟨n, hn⟩ := hs (g⁻¹ • a) (g⁻¹ • b) (fix a ha) (fix b hb)
  let c : M23 := MulAut.conj g ((s ^ n.val).val)
  have hc : c ∈ centralizer ({t} : Set M23) := by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (MulAut.conj g)
      (mem_centralizer_singleton_iff.mp (s ^ n.val).property)
    simpa only [map_mul, show MulAut.conj g involutionRepresentative = t from hg] using he
  refine ⟨⟨c, hc⟩, ?_⟩
  change (g * ((s ^ n.val).val) * g⁻¹) • a = b
  rw [mul_smul, mul_smul, show ((s ^ n.val).val) • (g⁻¹ • a) = g⁻¹ • b from hn,
    smul_inv_smul]

/-- Involutions in the degree-22 Mathieu group form a single conjugacy class. -/
theorem m22_involutions_isConj (u v : M22) (hu : orderOf u = 2) (hv : orderOf v = 2) :
    IsConj u v := by
  let e := m23EquivM22PointStabilizer
  let u' : M23 := e u
  let v' : M23 := e v
  have hu' : orderOf u' = 2 := (Subgroup.orderOf_coe _).trans ((e.orderOf_eq u).trans hu)
  have hv' : orderOf v' = 2 := (Subgroup.orderOf_coe _).trans ((e.orderOf_eq v).trans hv)
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj u' v' hu' hv')
  have hfix : v' • (g • (9 : Fin 23)) = g • (9 : Fin 23) := by
    rw [← hg]
    simp only [mul_smul, inv_smul_smul]
    rw [show u' • (9 : Fin 23) = 9 from (e u).property]
  obtain ⟨c, hc⟩ := centralizer_transitive_fixed v' hv'
    (g • (9 : Fin 23)) 9 hfix (e v).property
  let k : MulAction.stabilizer M23 (9 : Fin 23) := ⟨(c : M23) * g, by
    simpa only [MulAction.mem_stabilizer_iff, mul_smul] using hc⟩
  apply isConj_iff.mpr
  refine ⟨e.symm k, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
  apply Subtype.ext
  change ((c : M23) * g) * u' * ((c : M23) * g)⁻¹ = v'
  calc
    _ = (c : M23) * (g * u' * g⁻¹) * (c : M23)⁻¹ := by group
    _ = (c : M23) * v' * (c : M23)⁻¹ := by rw [hg]
    _ = v' := by rw [mem_centralizer_singleton_iff.mp c.property]; group

/-- Fixed points transform by the actual conjugating permutation. -/
theorem m22FixedPoints_conj (g u : M22) :
    m22FixedPoints (MulAut.conj g u) = g • m22FixedPoints u := by
  ext a
  rw [mem_m22FixedPoints, Finset.mem_smul_finset]
  constructor
  · intro ha
    refine ⟨g⁻¹ • a, (mem_m22FixedPoints _ _).mpr ?_, smul_inv_smul _ _⟩
    have he := congrArg (fun x : Fin 22 => g⁻¹ • x) ha
    simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using he
  · rintro ⟨b, hb, rfl⟩
    rw [mem_m22FixedPoints] at hb
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, hb]

/-- Pointwise kernels transform by the same conjugation as the hexad. -/
theorem m22HexadPointwiseKernel_smul (g : M22) (B : Finset (Fin 22)) :
    m22HexadPointwiseKernel (g • B) =
      (m22HexadPointwiseKernel B).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_m22HexadPointwiseKernel, mem_map_equiv, mem_m22HexadPointwiseKernel]
  constructor
  · intro hx a ha
    have he := congrArg (fun y : Fin 22 => g⁻¹ • y)
      (hx (g • a) (Finset.smul_mem_smul_finset ha))
    simpa only [MulAut.conj_symm_apply, mul_smul, inv_smul_smul] using he
  · intro hx a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_smul_finset.mp ha
    have he := congrArg (fun y : Fin 22 => g • y) (hx b hb)
    simpa only [MulAut.conj_symm_apply, mul_smul, smul_inv_smul] using he

end Sporadic.Mathieu
