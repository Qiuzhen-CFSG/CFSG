module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants

/-!
# Fixed and commutator spaces of nonsingular vector stabilizers

Explicit transvections show that every vector and every covector in dimension
at least two is a displacement for the full linear group. The pairing-one
splitting then computes both the fixed space and the commutator space of its
pair stabilizer. The actual inner-stabilizer equivalence transports these
identities without changing their embeddings in the natural-plus-dual space.

The commutator space is Mathlib's coinvariant kernel, the span of the actual
action differences. The action formulas retain the natural kernel action and
its contragredient on the complementary annihilator.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(4),
printed p.390, with the nonsingular pair independent of the pure-vector Sylow
marking as required by the source correction.
-/

@[expose] public section

namespace BinaryNaturalDual.VectorStabilizers
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem exists_outside_line [FiniteDimensional (ZMod 2) V]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) {w : V} (hw : w ≠ 0) :
    ∃ v : V, v ∉ Submodule.span (ZMod 2) {w} := by
  have hne : Submodule.span (ZMod 2) {w} ≠ ⊤ := by
    intro he
    have hf := finrank_span_singleton hw (K := ZMod 2)
    rw [he, finrank_top] at hf
    omega
  obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  exact ⟨v, hv⟩

/-- Every vector in dimension at least two is a displacement for some linear automorphism. -/
theorem exists_natural_displacement [FiniteDimensional (ZMod 2) V]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) (w : V) :
    ∃ (g : BinaryLinear.GL V) (v : V), g v - v = w := by
  by_cases hw : w = 0
  · exact ⟨1, 0, by simp [hw]⟩
  obtain ⟨v, hv⟩ := exists_outside_line hd hw
  obtain ⟨q, hqv, hqw⟩ := (Submodule.span (ZMod 2) {w}).exists_le_ker_of_notMem hv
  have hqv1 : q v = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hqv
  refine ⟨BinaryLinear.transvection w q (hqw (Submodule.mem_span_singleton_self w)), v, ?_⟩
  change v + q v • w - v = w
  simp [hqv1]

/-- The full linear group in dimension at least two has no nonzero fixed vector. -/
theorem natural_fixed_eq_zero [FiniteDimensional (ZMod 2) V]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) {v : V}
    (hv : ∀ g : BinaryLinear.GL V, g v = v) : v = 0 := by
  by_contra hv0
  obtain ⟨w, hw⟩ := exists_outside_line hd hv0
  have hw0 : w ≠ 0 := by intro he; exact hw (he ▸ Submodule.zero_mem _)
  have hline : Submodule.span (ZMod 2) {w} ≠ ⊥ := by
    intro he
    exact hw0 (by simpa [he] using Submodule.mem_span_singleton_self (R := ZMod 2) w)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    ((BinaryLinear.mem_iff_fixed_radical hline v).mpr (fun g _ => hv g))
  have ha0 : a ≠ 0 := by intro he; exact hv0 (by simpa [he] using ha.symm)
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ ha0
  have hwv : w = v := by simpa [ha1] using ha
  apply hw
  rw [hwv]
  exact Submodule.mem_span_singleton_self v

/-- Every covector is a displacement for a contragredient linear automorphism. -/
theorem exists_dual_displacement [FiniteDimensional (ZMod 2) V]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) (q : Module.Dual (ZMod 2) V) :
    ∃ (g : BinaryLinear.GL V) (p : Module.Dual (ZMod 2) V), g.symm.dualMap p - p = q := by
  by_cases hq : q = 0
  · exact ⟨1, 0, by simp [hq]⟩
  have hk : q.ker ≠ ⊥ := by
    intro he
    have hf := Module.Dual.finrank_ker_add_one_of_ne_zero hq
    rw [he, finrank_bot] at hf
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  obtain ⟨p, hp, _⟩ := (⊥ : Submodule (ZMod 2) V).exists_le_ker_of_notMem
    (show w ∉ (⊥ : Submodule (ZMod 2) V) from hw0)
  have hp1 : p w = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hp
  refine ⟨BinaryLinear.transvection w q hw, p, ?_⟩
  ext v
  change p (v + q v • w) - p v = q v
  simp [hp1]

/-- A fixed covector for the full natural group vanishes. -/
theorem dual_fixed_eq_zero [FiniteDimensional (ZMod 2) V]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) {q : Module.Dual (ZMod 2) V}
    (hq : ∀ (g : BinaryLinear.GL V) (v : V), q (g v) = q v) : q = 0 := by
  ext w
  obtain ⟨g, v, rfl⟩ := exists_natural_displacement hd w
  simp [hq]

variable {x : V} {f : Module.Dual (ZMod 2) V}

/-- The natural fixed space of the pairing-one stabilizer is precisely its marked line. -/
theorem pair_fixed_natural_iff [FiniteDimensional (ZMod 2) V]
    (h : f x = 1) (hd : 2 ≤ Module.finrank (ZMod 2) f.ker) (v : V) :
    (∀ g : pairStabilizer x f, g.val v = v) ↔ v ∈ Submodule.span (ZMod 2) {x} := by
  constructor
  · intro hv
    have hz : kernelProjection h v = 0 := natural_fixed_eq_zero hd (fun k => by
      let g := (pairStabilizerEquivKernel h).symm k
      have he := kernelProjection_equivariant h g v
      rw [hv g] at he
      have hk : kernelAction x f g = k := (pairStabilizerEquivKernel h).apply_symm_apply k
      rw [hk] at he
      exact he.symm)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨f v, ?_⟩
    have hh := congrArg (fun w : f.ker => (w : V)) hz
    exact (sub_eq_zero.mp hh).symm
  · intro hv g
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, g.property.1]

/-- The dual fixed space of the pairing-one stabilizer is precisely its marked covector line. -/
theorem pair_fixed_dual_iff [FiniteDimensional (ZMod 2) V]
    (h : f x = 1) (hd : 2 ≤ Module.finrank (ZMod 2) f.ker)
    (q : Module.Dual (ZMod 2) V) :
    (∀ g : pairStabilizer x f, g.val.symm.dualMap q = q) ↔
      q ∈ Submodule.span (ZMod 2) {f} := by
  constructor
  · intro hq
    have hz : q.comp f.ker.subtype = 0 := dual_fixed_eq_zero hd (fun k v => by
      let g := (pairStabilizerEquivKernel h).symm k
      have he := LinearMap.congr_fun (hq g⁻¹) v
      change q (g.val v) = q v at he
      have hk : kernelAction x f g = k := (pairStabilizerEquivKernel h).apply_symm_apply k
      change q (k v) = q v
      rw [← hk]
      exact he)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨q x, ?_⟩
    ext v
    have hh := LinearMap.congr_fun hz (kernelProjection h v)
    change q (v - f v • x) = 0 at hh
    simp only [map_sub, map_smul, smul_eq_mul] at hh
    change q x * f v = q v
    rw [mul_comm]
    exact (sub_eq_zero.mp hh).symm
  · intro hq g
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hq
    ext v
    change a * f (g.val.symm v) = a * f v
    rw [show f (g.val.symm v) = f v from (g⁻¹).property.2 v]

/-- The literal paired representation of the matrix pair stabilizer. -/
def pairRepresentation (x : V) (f : Module.Dual (ZMod 2) V) :
    Representation (ZMod 2) (pairStabilizer x f) (BinaryNaturalDual.Space V) :=
  naturalDualRepresentation.comp (pairStabilizer x f).subtype

/-- Exactly the two marked lines are fixed by the nonsingular inner stabilizer. -/
theorem pair_invariants [FiniteDimensional (ZMod 2) V]
    (h : f x = 1) (hd : 2 ≤ Module.finrank (ZMod 2) f.ker) :
    Representation.invariants (pairRepresentation x f) =
      (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f}) := by
  ext v
  rcases v with ⟨v,q⟩
  change (∀ g : pairStabilizer x f, naturalDualRepresentation g.val (v,q) = (v,q)) ↔ _
  simp only [naturalDualRepresentation_apply, Prod.mk.injEq, forall_and,
    pair_fixed_natural_iff h hd, pair_fixed_dual_iff h hd, Submodule.mem_prod]

/-- The commutator space is exactly the product of the two complementary hyperplanes. -/
theorem pair_commutator [FiniteDimensional (ZMod 2) V]
    (h : f x = 1) (hd : 2 ≤ Module.finrank (ZMod 2) f.ker) :
    Representation.Coinvariants.ker (pairRepresentation x f) = f.ker.prod (annihilator x) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change (naturalDualRepresentation g.val v - v) ∈ f.ker.prod (annihilator x)
    rw [naturalDualRepresentation_apply]
    constructor
    · change f (g.val v.1 - v.1) = 0
      rw [map_sub, g.property.2, sub_self]
    · change v.2 (g.val.symm x) - v.2 x = 0
      rw [show g.val.symm x = x from (g⁻¹).property.1, sub_self]
  · intro v hv
    have hn : (v.1, (0 : Module.Dual (ZMod 2) V)) ∈
        Representation.Coinvariants.ker (pairRepresentation x f) := by
      obtain ⟨k, w, hw⟩ := exists_natural_displacement hd (⟨v.1, hv.1⟩ : f.ker)
      let g := (pairStabilizerEquivKernel h).symm k
      have hk : kernelAction x f g = k := (pairStabilizerEquivKernel h).apply_symm_apply k
      apply Representation.Coinvariants.mem_ker_of_eq g (w.val, 0)
      change naturalDualRepresentation g.val (w.val,0) - (w.val,0) = (v.1,0)
      apply Prod.ext
      · rw [naturalDualRepresentation_apply]
        change g.val w - w = v.1
        have he := congrArg (fun y : f.ker => (y : V)) hw
        rwa [← hk] at he
      · simp only [naturalDualRepresentation_apply, map_zero, Prod.snd_sub, sub_self]
    have hq : ((0 : V), v.2) ∈ Representation.Coinvariants.ker (pairRepresentation x f) := by
      let q : annihilator x := ⟨v.2, hv.2⟩
      obtain ⟨k, p, hp⟩ := exists_dual_displacement hd (annihilatorEquivKernelDual h q)
      let g := (pairStabilizerEquivKernel h).symm k
      let a := (annihilatorEquivKernelDual h).symm p
      have hk : kernelAction x f g = k := (pairStabilizerEquivKernel h).apply_symm_apply k
      have he : annihilatorAction x f g a - a = q := by
        apply (annihilatorEquivKernelDual h).injective
        calc
          annihilatorEquivKernelDual h (annihilatorAction x f g a - a) =
              annihilatorEquivKernelDual h (annihilatorAction x f g a) -
                annihilatorEquivKernelDual h a := (annihilatorEquivKernelDual h).map_sub _ _
          _ = k.symm.dualMap p - p := by
            rw [annihilatorEquivKernelDual_equivariant, hk, LinearEquiv.apply_symm_apply]
          _ = annihilatorEquivKernelDual h q := hp
      apply Representation.Coinvariants.mem_ker_of_eq g (0, a.val)
      change naturalDualRepresentation g.val (0,a.val) - (0,a.val) = (0,v.2)
      apply Prod.ext
      · simp only [naturalDualRepresentation_apply, map_zero, Prod.fst_sub, sub_self]
      · rw [naturalDualRepresentation_apply]
        exact congrArg (fun y : annihilator x => y.val) he
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      (Representation.Coinvariants.ker (pairRepresentation x f)).add_mem hn hq

end BinaryNaturalDual.VectorStabilizers

namespace BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic

/-- The group comparison remembers the actual conjugating matrix. -/
theorem innerStabilizerEquivPair_conj {n : ℕ} (d : CoordinateAction n)
    (x : BinaryLinear.OuterCyclic.Space n)
    (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
    (a : innerStabilizer d (x,f)) :
    MulAut.conj ((innerStabilizerEquivPair d x f a).val) = a.val := by
  let e := (pairStabilizer x f).equivMapOfInjective MulAut.conj (inner_injective d)
  have he := e.apply_symm_apply
    ((MulEquiv.subgroupCongr (innerStabilizer_eq_map_pairStabilizer d x f)) a)
  exact congrArg (fun z : (pairStabilizer x f).map MulAut.conj => z.val) he

/-- The action of the actual inner stabilizer is its identified natural-plus-dual action. -/
theorem innerStabilizer_action {n : ℕ} (d : CoordinateAction n)
    (x : BinaryLinear.OuterCyclic.Space n)
    (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
    (a : innerStabilizer d (x,f)) (v : CoordinateSpace n) :
    d.representation a.val v =
      naturalDualRepresentation ((innerStabilizerEquivPair d x f a).val) v := by
  rw [← innerStabilizerEquivPair_conj d x f a, d.on_inner]

/-- The complement in the natural summand carries the actual full natural kernel action. -/
theorem inner_kernel_action {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : innerStabilizer d (x,f)) (w : f.ker) :
    d.representation a.val (w.val,0) =
      ((innerStabilizerEquivKernel d h a w : BinaryLinear.OuterCyclic.Space n),0) := by
  rw [innerStabilizer_action, naturalDualRepresentation_apply, map_zero]
  rfl

/-- Evaluation on the natural complement gives exactly its contragredient action. -/
theorem inner_dual_kernel_action {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : innerStabilizer d (x,f)) (q : annihilator x) (w : f.ker) :
    (d.representation a.val (0,q.val)).2 w =
      annihilatorEquivKernelDual h q ((innerStabilizerEquivKernel d h a).symm w) := by
  rw [innerStabilizer_action, naturalDualRepresentation_apply]
  rfl

/-- The restricted representation on the actual inner vector stabilizer. -/
def innerRepresentation {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) :
    Representation (ZMod 2) (innerStabilizer d v) (CoordinateSpace n) :=
  d.representation.comp (innerStabilizer d v).subtype

/-- The stabilizer comparison preserves the actual fixed space. -/
theorem inner_invariants_eq_pair {n : ℕ} (d : CoordinateAction n)
    (x : BinaryLinear.OuterCyclic.Space n)
    (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    Representation.invariants (innerRepresentation d (x,f)) =
      Representation.invariants (pairRepresentation x f) := by
  ext v
  change (∀ a : innerStabilizer d (x,f), d.representation a.val v = v) ↔
    (∀ g : pairStabilizer x f, naturalDualRepresentation g.val v = v)
  constructor
  · intro hv g
    have he := hv ((innerStabilizerEquivPair d x f).symm g)
    rwa [innerStabilizer_action, MulEquiv.apply_symm_apply] at he
  · intro hv a
    rw [innerStabilizer_action]
    exact hv _

/-- The stabilizer comparison preserves the commutator space, including its embedding. -/
theorem inner_commutator_eq_pair {n : ℕ} (d : CoordinateAction n)
    (x : BinaryLinear.OuterCyclic.Space n)
    (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    Representation.Coinvariants.ker (innerRepresentation d (x,f)) =
      Representation.Coinvariants.ker (pairRepresentation x f) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩, rfl⟩
    change d.representation a.val v - v ∈ _
    rw [innerStabilizer_action]
    exact Representation.Coinvariants.sub_mem_ker (ρ := pairRepresentation x f)
      (innerStabilizerEquivPair d x f a) v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩, rfl⟩
    have he := Representation.Coinvariants.sub_mem_ker (ρ := innerRepresentation d (x,f))
      ((innerStabilizerEquivPair d x f).symm g) v
    change d.representation (((innerStabilizerEquivPair d x f).symm g).val) v - v ∈ _ at he
    rw [innerStabilizer_action, MulEquiv.apply_symm_apply] at he
    exact he

/-- The fixed space of the actual inner nonsingular stabilizer is the two marked lines. -/
theorem inner_invariants {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Representation.invariants (innerRepresentation d (x,f)) =
      (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f}) := by
  rw [inner_invariants_eq_pair]
  apply pair_invariants h
  have hd : Module.finrank (ZMod 2) f.ker + 1 = n := by
    simpa only [BinaryLinear.OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin] using finrank_kernel h
  omega

/-- The commutator space of the actual inner nonsingular stabilizer is `ker(f) ⊕ ann(x)`. -/
theorem inner_commutator {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Representation.Coinvariants.ker (innerRepresentation d (x,f)) =
      f.ker.prod (annihilator x) := by
  rw [inner_commutator_eq_pair]
  apply pair_commutator h
  have hd : Module.finrank (ZMod 2) f.ker + 1 = n := by
    simpa only [BinaryLinear.OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin] using finrank_kernel h
  omega

end BinaryNaturalDual.VectorStabilizers
