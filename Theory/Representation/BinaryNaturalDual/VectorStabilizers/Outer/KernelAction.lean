module

public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Modules
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer.Extension


/-!
# Conjugation on the actual kernel group

Restriction to the covector kernel identifies the inner stabilizer with its
full linear group. Conjugation in the full stabilizer therefore acts on that
actual linear group. For an outer element, its natural-to-dual block gives an
injective map from the kernel to its dual, intertwining the conjugated action
with the exact contragredient action.

Two transvections show that the natural and dual modules in dimension at least
three admit no injective intertwiner. Thus an outer element cannot centralize
the kernel group. The center of the binary linear group is trivial, so the
entire conjugation homomorphism is faithful.

Source: Aschbacher–Smith, H.9.1(4), printed p.390; the elementary transvection
argument is the binary analogue of the natural/dual separation used in 13.8.20.
-/

@[expose] public section

open BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.VectorStabilizers

private theorem no_injective_natural_dual {m : ℕ} (hm : 3 ≤ m)
    (e : BinaryLinear.OuterCyclic.Space m →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space m))
    (hinj : Function.Injective e)
    (he : ∀ (g : LinearGroup m) v, e (g v) = g.symm.dualMap (e v)) : False := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  let k : Fin m := ⟨2, by omega⟩
  let b : BinaryLinear.OuterCyclic.Space m := Pi.single i 1
  let v : BinaryLinear.OuterCyclic.Space m := Pi.single j 1 + Pi.single k 1
  let qj : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space m) := LinearMap.proj j
  let qk : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space m) := LinearMap.proj k
  have hj : qj b = 0 := by simp [qj, b, i, j]
  have hk : qk b = 0 := by simp [qk, b, i, k]
  let tj := BinaryLinear.transvection b qj hj
  let tk := BinaryLinear.transvection b qk hk
  have hvj : tj v = v + b := by
    change v + qj v • b = v + b
    simp [qj, v, j, k]
  have hvk : tk v = v + b := by
    change v + qk v • b = v + b
    simp [qk, v, j, k]
  have hr (w) : e b w = qj w * e v b := by
    have hh := LinearMap.congr_fun (he tj v) w
    rw [hvj, map_add] at hh
    change e v w + e b w = e v (w + qj w • b) at hh
    simpa only [map_add, map_smul, smul_eq_mul, add_right_inj] using hh
  have hs (w) : e b w = qk w * e v b := by
    have hh := LinearMap.congr_fun (he tk v) w
    rw [hvk, map_add] at hh
    change e v w + e b w = e v (w + qk w • b) at hh
    simpa only [map_add, map_smul, smul_eq_mul, add_right_inj] using hh
  have hz : e v b = 0 := by
    have hh := (hr (Pi.single j 1)).symm.trans (hs (Pi.single j 1))
    simpa [qj, qk, j, k] using hh
  have hb : e b = e 0 := by
    apply LinearMap.ext
    intro w
    rw [hr, hz, mul_zero, map_zero, LinearMap.zero_apply]
  have hb0 := congrFun (hinj hb) i
  simp [b] at hb0

/-- The inner subgroup of the full stabilizer acts as the full linear group of the kernel. -/
noncomputable def innerInFullEquivKernel {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    innerInFull d (x,f) ≃* BinaryLinear.GL f.ker :=
  (innerInFullEquiv d (x,f)).trans (innerStabilizerEquivKernel d h)

/-- Extend a kernel automorphism to the actual inner subgroup of the full stabilizer. -/
noncomputable def kernelInner {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    BinaryLinear.GL f.ker →* fullStabilizer d (x,f) :=
  (innerInFull d (x,f)).subtype.comp (innerInFullEquivKernel d h).symm.toMonoidHom

/-- Conjugation by the actual full stabilizer, in the published kernel coordinates. -/
noncomputable def kernelConjugation {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    fullStabilizer d (x,f) →* MulAut (BinaryLinear.GL f.ker) :=
  (MulAut.congr (innerInFullEquivKernel d h)).toMonoidHom.comp MulAut.conjNormal

/-- The kernel-group homomorphism respects the actual ambient conjugation. -/
theorem kernelInner_conj {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : fullStabilizer d (x,f)) (k : BinaryLinear.GL f.ker) :
    kernelInner d h (kernelConjugation d h a k) = a * kernelInner d h k * a⁻¹ := by
  exact congrArg Subtype.val ((innerInFullEquivKernel d h).symm_apply_apply
    (MulAut.conjNormal a ((innerInFullEquivKernel d h).symm k)))

/-- The embedded kernel group induces exactly its inner automorphisms. -/
theorem kernelConjugation_inner {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (k : BinaryLinear.GL f.ker) :
    kernelConjugation d h (kernelInner d h k) = MulAut.conj k := by
  apply MulEquiv.ext
  intro t
  change (innerInFullEquivKernel d h)
    ((innerInFullEquivKernel d h).symm k * (innerInFullEquivKernel d h).symm t *
      ((innerInFullEquivKernel d h).symm k)⁻¹) = k * t * k⁻¹
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

/-- The embedded kernel group has its actual natural action on the kernel. -/
theorem kernelInner_action {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (k : BinaryLinear.GL f.ker) (w : f.ker) :
    d.representation (kernelInner d h k).val (w.val,0) = ((k w).val,0) := by
  have hh := inner_kernel_action d h
    (innerInFullEquiv d (x,f) ((innerInFullEquivKernel d h).symm k)) w
  have he : innerStabilizerEquivKernel d h
    (innerInFullEquiv d (x,f) ((innerInFullEquivKernel d h).symm k)) = k :=
    (innerInFullEquivKernel d h).apply_symm_apply k
  rw [he] at hh
  exact hh

/-- The embedded kernel group acts contragrediently on the complementary annihilator. -/
theorem kernelInner_dual_action {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (k : BinaryLinear.GL f.ker) (q : annihilator x) (w : f.ker) :
    (d.representation (kernelInner d h k).val (0,q.val)).2 w = q.val (k.symm w) := by
  have hh := inner_dual_kernel_action d h
    (innerInFullEquiv d (x,f) ((innerInFullEquivKernel d h).symm k)) q w
  have he : innerStabilizerEquivKernel d h
    (innerInFullEquiv d (x,f) ((innerInFullEquivKernel d h).symm k)) = k :=
    (innerInFullEquivKernel d h).apply_symm_apply k
  rw [he] at hh
  exact hh

/-- The natural-to-dual block of an actor, restricted to the actual covector kernel. -/
def outerKernelDual {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (a : fullStabilizer d (x,f)) : f.ker →ₗ[ZMod 2] Module.Dual (ZMod 2) f.ker where
  toFun w := (d.representation a.val (w.val,0)).2.comp f.ker.subtype
  map_add' u v := by
    ext w
    change (d.representation a.val ((u + v).val,0)).2 w = _
    have hh : ((u + v).val, (0 : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))) =
      (u.val,0) + (v.val,0) := by simp
    rw [hh, map_add]
    rfl
  map_smul' c u := by
    ext w
    change (d.representation a.val ((c • u).val,0)).2 w = _
    have hh : ((c • u).val, (0 : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))) =
      c • (u.val,0) := by simp
    rw [hh, map_smul]
    rfl

private theorem outer_graph_form {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (a : fullStabilizer d (x,f)) (hout : a.val ∉ MulAut.innerSubgroup (LinearGroup n)) :
    ∃ g : LinearGroup n, a.val = graphLinear n * MulAut.conj g := by
  obtain ⟨g, hi | hg⟩ := inner_graph hn a.val
  · exact False.elim (hout ⟨g, hi.symm⟩)
  · exact ⟨g, hg⟩

/-- An outer stabilizer element sends every pure natural vector into the dual summand. -/
theorem outer_pure_fst {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (a : fullStabilizer d (x,f)) (hout : a.val ∉ MulAut.innerSubgroup (LinearGroup n))
    (w : BinaryLinear.OuterCyclic.Space n) : (d.representation a.val (w,0)).1 = 0 := by
  obtain ⟨g, hg⟩ := outer_graph_form hn d a hout
  rw [hg]
  exact graph_inner_pure d g w

/-- The outer block sends the covector kernel into the annihilator of the marked vector. -/
theorem outer_pure_annihilator {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (a : fullStabilizer d (x,f)) (hout : a.val ∉ MulAut.innerSubgroup (LinearGroup n))
    (w : f.ker) : (d.representation a.val (w.val,0)).2 ∈ annihilator x := by
  obtain ⟨g, hg⟩ := outer_graph_form hn d a hout
  have hf := congrArg Prod.fst a.property
  change (d.representation a.val (x,f)).1 = x at hf
  rw [hg, map_mul, Module.End.mul_apply, d.on_inner, d.on_graph,
    naturalDualRepresentation_apply, coordinateSwap_apply] at hf
  have hh : g.symm.dualMap f = dotProductEquiv (ZMod 2) (Fin n) x := by
    rw [← hf, LinearEquiv.apply_symm_apply]
  change (d.representation a.val (w.val,0)).2 x = 0
  rw [hg, map_mul, Module.End.mul_apply, d.on_inner, d.on_graph,
    naturalDualRepresentation_apply, coordinateSwap_apply]
  change dotProduct (g w) x = 0
  rw [dotProduct_comm]
  change (dotProductEquiv (ZMod 2) (Fin n) x) (g w) = 0
  rw [← hh]
  change f (g.symm (g w)) = 0
  rw [g.symm_apply_apply]
  exact w.property

/-- Every outer fixer of a nonsingular pair exchanges its two marked pure components. -/
theorem outer_swaps_components {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (a : fullStabilizer d (x,f)) (hout : a.val ∉ MulAut.innerSubgroup (LinearGroup n)) :
    d.representation a.val (x,0) = (0,f) ∧ d.representation a.val (0,f) = (x,0) := by
  obtain ⟨g,hg⟩ := outer_graph_form hn d a hout
  have he := a.property
  change d.representation a.val (x,f) = (x,f) at he
  rw [hg, map_mul, Module.End.mul_apply, d.on_inner, d.on_graph,
    naturalDualRepresentation_apply, coordinateSwap_apply] at he
  have he1 := congrArg (fun v : CoordinateSpace n => v.1) he
  have he2 := congrArg (fun v : CoordinateSpace n => v.2) he
  constructor
  · rw [hg, map_mul, Module.End.mul_apply, d.on_inner, d.on_graph,
      naturalDualRepresentation_apply, coordinateSwap_apply, map_zero, map_zero]
    exact Prod.ext rfl he2
  · rw [hg, map_mul, Module.End.mul_apply, d.on_inner, d.on_graph,
      naturalDualRepresentation_apply, coordinateSwap_apply, map_zero, map_zero]
    exact Prod.ext he1 rfl

/-- For an outer fixer of a pairing-one pair, the restricted dual block is faithful. -/
theorem outerKernelDual_injective {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : fullStabilizer d (x,f)) (hout : a.val ∉ MulAut.innerSubgroup (LinearGroup n)) :
    Function.Injective (outerKernelDual d a) := by
  intro u v huv
  have he : (d.representation a.val (u.val,0)).2 =
      (d.representation a.val (v.val,0)).2 := by
    exact (fun hh => congrArg Subtype.val hh)
      ((annihilatorEquivKernelDual h).injective (a₁ := ⟨_, outer_pure_annihilator hn d a hout u⟩)
        (a₂ := ⟨_, outer_pure_annihilator hn d a hout v⟩) huv)
  obtain ⟨g, hg⟩ := outer_graph_form hn d a hout
  simp only [hg, map_mul, Module.End.mul_apply] at he
  rw [d.on_inner, d.on_inner, d.on_graph, d.on_graph,
    naturalDualRepresentation_apply, naturalDualRepresentation_apply,
    coordinateSwap_apply, coordinateSwap_apply] at he
  exact Subtype.ext (g.injective ((dotProductEquiv (ZMod 2) (Fin n)).injective he))

/-- The outer block intertwines kernel conjugation with the actual contragredient action. -/
theorem outerKernelDual_intertwines {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : fullStabilizer d (x,f)) (hout : a.val ∉ MulAut.innerSubgroup (LinearGroup n))
    (k : BinaryLinear.GL f.ker) (u : f.ker) :
    outerKernelDual d a (k u) = (kernelConjugation d h a k).symm.dualMap
      (outerKernelDual d a u) := by
  have hm : a * kernelInner d h k = kernelInner d h (kernelConjugation d h a k) * a := by
    rw [kernelInner_conj]
    group
  have hr := congrArg (fun b : fullStabilizer d (x,f) =>
    d.representation b.val (u.val,0)) hm
  change d.representation (a.val * (kernelInner d h k).val) (u.val,0) =
    d.representation ((kernelInner d h (kernelConjugation d h a k)).val * a.val) (u.val,0) at hr
  simp only [map_mul, Module.End.mul_apply, kernelInner_action] at hr
  have hp : d.representation a.val (u.val,0) =
    (0, (d.representation a.val (u.val,0)).2) := Prod.ext (outer_pure_fst hn d a hout u) rfl
  rw [hp] at hr
  ext w
  have hh := congrArg (fun z : CoordinateSpace n => z.2 w) hr
  rw [kernelInner_dual_action d h _
    ⟨_, outer_pure_annihilator hn d a hout u⟩] at hh
  exact hh

private theorem outer_not_kernel {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : fullStabilizer d (x,f)) (hout : a.val ∉ MulAut.innerSubgroup (LinearGroup n))
    (ha : kernelConjugation d h a = 1) : False := by
  let c := kernelCoordinates h
  let e := (c.symm.dualMap.toLinearMap.comp (outerKernelDual d a)).comp c.symm.toLinearMap
  apply no_injective_natural_dual (by omega : 3 ≤ n - 1) e
    (c.symm.dualMap.injective.comp ((outerKernelDual_injective hn d h a hout).comp
      c.symm.injective))
  intro g v
  apply LinearMap.ext
  intro w
  let k : BinaryLinear.GL f.ker := (c.trans g).trans c.symm
  have hh := LinearMap.congr_fun (outerKernelDual_intertwines hn d h a hout k (c.symm v))
    (c.symm w)
  rw [ha] at hh
  change outerKernelDual d a (k (c.symm v)) (c.symm w) =
    outerKernelDual d a (c.symm v) (k.symm (c.symm w)) at hh
  change outerKernelDual d a (c.symm (g v)) (c.symm w) =
    outerKernelDual d a (c.symm v) (c.symm (g.symm w))
  simpa only [k, LinearEquiv.trans_apply, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply] using hh

private theorem kernel_conj_injective {n : ℕ} (hn : n = 4 ∨ n = 5)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Function.Injective (MulAut.conj : BinaryLinear.GL f.ker →* MulAut (BinaryLinear.GL f.ker)) := by
  apply MulAut.conj_injective_of_center_eq_bot
  apply le_bot_iff.mp
  intro k hk
  let e := (kernelGroupCoordinates h).trans (slEquivLinear (n - 1)).symm
  have hc := (Subgroup.centerCongr e ⟨k,hk⟩).property
  have he : e k = 1 := by
    exact Subgroup.mem_bot.mp ((binary_center_eq_bot (by omega : 0 < n - 1)).le hc)
  exact Subgroup.mem_bot.mpr (e.map_eq_one_iff.mp he)

/-- The full nonsingular stabilizer acts faithfully by conjugation on its kernel group. -/
theorem kernelConjugation_injective {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Function.Injective (kernelConjugation d h) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  have ha1 : kernelConjugation d h a = 1 := ha
  have hain : a ∈ innerInFull d (x,f) := by
    apply (mem_innerInFull d (x,f) a).mpr
    by_contra hout
    exact outer_not_kernel hn d h a hout ha1
  let b : innerInFull d (x,f) := ⟨a,hain⟩
  let k := innerInFullEquivKernel d h b
  have he : kernelInner d h k = a :=
    congrArg Subtype.val ((innerInFullEquivKernel d h).symm_apply_apply b)
  have hk : k = 1 := kernel_conj_injective hn h
    ((kernelConjugation_inner d h k).symm.trans (by rw [he, ha1, map_one]))
  change a = 1
  rw [← he, hk, map_one]

end BinaryNaturalDual.VectorStabilizers
