module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Basic

/-!
# Commutator spaces of a pure-vector stabilizer

The radical transvections along x produce every covector annihilating x
as a dual displacement, and produce x as a natural displacement. A Levi
complement supplies the remaining natural hyperplane. Consequently the
commutator space is exactly X ⊕ ann(x), with both summands separately marked.

Source: Aschbacher–Smith, H.9.1(3), printed pp.389–390.
-/

@[expose] public section
namespace BinaryNaturalDual.VectorStabilizers.Pure
open BinaryLinear
open Theory.LinearAlgebra
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Every nonzero binary vector admits a covector paired to one. -/
theorem exists_pairing {x : V} (hx : x ≠ 0) : ∃ f : Module.Dual (ZMod 2) V, f x = 1 := by
  obtain ⟨f, hf, _⟩ := (⊥ : Submodule (ZMod 2) V).exists_le_ker_of_notMem hx
  exact ⟨f, (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hf⟩

/-- The exact action of the matrix point stabilizer on the doubled module. -/
def pointRepresentation (x : V) :
    Representation (ZMod 2) (pointStabilizer x) (BinaryNaturalDual.Space V) :=
  naturalDualRepresentation.comp (pointStabilizer x).subtype

/-- Covectors annihilating x are all actual displacements of the point radical. -/
theorem dual_displacement {x : V} (hx : x ≠ 0) {q : Module.Dual (ZMod 2) V}
    (hq : q ∈ annihilator x) :
    ∃ (g : pointStabilizer x) (f : Module.Dual (ZMod 2) V),
      g.val.symm.dualMap f - f = q := by
  obtain ⟨f, hf⟩ := exists_pairing hx
  refine ⟨⟨transvection x q hq, ?_⟩, f, ?_⟩
  · change x + q x • x = x
    simp [show q x = 0 from hq]
  · ext v
    change f (v + q v • x) - f v = q v
    simp [hf]

/-- The marked vector is itself a displacement of a radical transvection. -/
theorem marked_displacement [FiniteDimensional (ZMod 2) V]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) {x : V} (hx : x ≠ 0) :
    ∃ (g : pointStabilizer x) (v : V), g.val v - v = x := by
  have hline : Submodule.span (ZMod 2) {x} ≠ ⊤ := by
    intro he
    have hh := finrank_span_singleton (K := ZMod 2) hx
    rw [he, finrank_top] at hh
    omega
  obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hline)
  obtain ⟨q, hqv, hqx⟩ := (Submodule.span (ZMod 2) {x}).exists_le_ker_of_notMem hv
  have hqx0 : q x = 0 := hqx (Submodule.mem_span_singleton_self x)
  have hqv1 : q v = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hqv
  refine ⟨⟨transvection x q hqx0, ?_⟩, v, ?_⟩
  · change x + q x • x = x
    simp [hqx0]
  · change v + q v • x - v = x
    simp [hqv1]

/-- The doubled commutator space, with its actual embeddings in X ⊕ X*. -/
theorem point_commutator [FiniteDimensional (ZMod 2) V]
    (hd : 3 ≤ Module.finrank (ZMod 2) V) {x : V} (hx : x ≠ 0) :
    Representation.Coinvariants.ker (pointRepresentation x) =
      (⊤ : Submodule (ZMod 2) V).prod (annihilator x) := by
  obtain ⟨f, hf⟩ := exists_pairing hx
  have hk : 2 ≤ Module.finrank (ZMod 2) f.ker := by
    have hh := finrank_kernel hf
    omega
  have hpair : Representation.Coinvariants.ker (pairRepresentation x f) ≤
      Representation.Coinvariants.ker (pointRepresentation x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker (ρ := pointRepresentation x)
      ⟨g.val, g.property.1⟩ v
  have hxmem : (x, (0 : Module.Dual (ZMod 2) V)) ∈
      Representation.Coinvariants.ker (pointRepresentation x) := by
    obtain ⟨g,v,hv⟩ := marked_displacement (by omega) hx
    apply Representation.Coinvariants.mem_ker_of_eq g (v,0)
    change naturalDualRepresentation g.val (v,0) - (v,0) = (x,0)
    simp [naturalDualRepresentation_apply, hv]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩, rfl⟩
    change (naturalDualRepresentation g.val v - v) ∈ _
    rw [naturalDualRepresentation_apply]
    constructor
    · trivial
    · change v.2 (g.val.symm x) - v.2 x = 0
      rw [show g.val.symm x = x from (g⁻¹).property, sub_self]
  · intro v hv
    have hp : ((kernelProjection hf v.1 : V), v.2) ∈
        Representation.Coinvariants.ker (pointRepresentation x) := by
      apply hpair
      rw [pair_commutator hf hk]
      exact ⟨(kernelProjection hf v.1).property, hv.2⟩
    have hh := (Representation.Coinvariants.ker (pointRepresentation x)).add_mem
      ((Representation.Coinvariants.ker (pointRepresentation x)).smul_mem (f v.1) hxmem) hp
    simpa only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add,
      kernelProjection_apply, add_sub_cancel] using hh

/-- The natural representation of the matrix point stabilizer. -/
def pointNaturalRepresentation (x : V) : Representation (ZMod 2) (pointStabilizer x) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (pointStabilizer x).subtype

/-- The contragredient representation of the same stabilizer. -/
def pointDualRepresentation (x : V) :
    Representation (ZMod 2) (pointStabilizer x) (Module.Dual (ZMod 2) V) where
  toFun g := g.val.symm.dualMap.toLinearMap
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- The full natural summand is generated by actual action differences. -/
theorem point_natural_commutator [FiniteDimensional (ZMod 2) V]
    (hd : 3 ≤ Module.finrank (ZMod 2) V) {x : V} (hx : x ≠ 0) :
    Representation.Coinvariants.ker (pointNaturalRepresentation x) = ⊤ := by
  apply top_unique
  intro v _
  have hh : (v, (0 : Module.Dual (ZMod 2) V)) ∈
      Representation.Coinvariants.ker (pointRepresentation x) := by
    rw [point_commutator hd hx]
    exact ⟨Submodule.mem_top, Submodule.zero_mem _⟩
  have hle : Representation.Coinvariants.ker (pointRepresentation x) ≤
      (Representation.Coinvariants.ker (pointNaturalRepresentation x)).comap
        (LinearMap.fst (ZMod 2) V (Module.Dual (ZMod 2) V)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩, rfl⟩
    change (naturalDualRepresentation g.val w - w).1 ∈
      Representation.Coinvariants.ker (pointNaturalRepresentation x)
    rw [naturalDualRepresentation_apply]
    exact Representation.Coinvariants.sub_mem_ker (ρ := pointNaturalRepresentation x) g w.1
  exact hle hh

/-- The dual commutator space is exactly the marked annihilator. -/
theorem point_dual_commutator {x : V} (hx : x ≠ 0) :
    Representation.Coinvariants.ker (pointDualRepresentation x) = annihilator x := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,q⟩, rfl⟩
    change q (g.val.symm x) - q x = 0
    rw [show g.val.symm x = x from (g⁻¹).property, sub_self]
  · intro q hq
    obtain ⟨g,f,hf⟩ := dual_displacement hx hq
    apply Representation.Coinvariants.mem_ker_of_eq g f
    exact hf

open BinaryLinear.OuterCyclic

/-- The hyperplane in H.9.1(3) has the precise dimension n−1. -/
theorem annihilator_finrank {n : ℕ} {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    Module.finrank (ZMod 2) (annihilator x) = n - 1 := by
  obtain ⟨f,hf⟩ := exists_pairing hx
  have hh := finrank_annihilator hf
  simp only [OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin] at hh
  change Module.finrank (ZMod 2) (annihilator x) + 1 = n at hh
  omega

/-- The matrix comparison preserves the exact doubled commutator space. -/
theorem inner_commutator {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    Representation.Coinvariants.ker (innerRepresentation d (x,0)) =
      (⊤ : Submodule (ZMod 2) (OuterCyclic.Space n)).prod (annihilator x) := by
  have he : Representation.Coinvariants.ker (innerRepresentation d (x,0)) =
      Representation.Coinvariants.ker (pointRepresentation x) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a,v⟩, rfl⟩
      change d.representation a.val v - v ∈ _
      rw [inner_action]
      exact Representation.Coinvariants.sub_mem_ker (ρ := pointRepresentation x)
        (innerEquivPoint d x a) v
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩, rfl⟩
      have hh := Representation.Coinvariants.sub_mem_ker (ρ := innerRepresentation d (x,0))
        ((innerEquivPoint d x).symm g) v
      change d.representation (((innerEquivPoint d x).symm g).val) v - v ∈ _ at hh
      rw [inner_action, MulEquiv.apply_symm_apply] at hh
      exact hh
  rw [he]
  exact point_commutator (by simpa only [OuterCyclic.Space, Module.finrank_pi,
    Fintype.card_fin] using (show 3 ≤ n by omega)) hx


/-- Natural action of the actual inner pure-vector stabilizer. -/
noncomputable def innerNaturalRepresentation {n : ℕ} (d : CoordinateAction n)
    (x : OuterCyclic.Space n) : Representation (ZMod 2) (innerStabilizer d (x,0)) (OuterCyclic.Space n) :=
  (pointNaturalRepresentation x).comp (innerEquivPoint d x).toMonoidHom

/-- Dual action of the same actual stabilizer. -/
noncomputable def innerDualRepresentation {n : ℕ} (d : CoordinateAction n)
    (x : OuterCyclic.Space n) : Representation (ZMod 2) (innerStabilizer d (x,0))
      (Module.Dual (ZMod 2) (OuterCyclic.Space n)) :=
  (pointDualRepresentation x).comp (innerEquivPoint d x).toMonoidHom

theorem innerNaturalRepresentation_apply {n : ℕ} (d : CoordinateAction n)
    (x : OuterCyclic.Space n) (a : innerStabilizer d (x,0)) (v : OuterCyclic.Space n) :
    innerNaturalRepresentation d x a v = (d.representation a.val (v,0)).1 := by
  rw [inner_action, naturalDualRepresentation_apply]
  rfl

theorem innerDualRepresentation_apply {n : ℕ} (d : CoordinateAction n)
    (x : OuterCyclic.Space n) (a : innerStabilizer d (x,0))
    (q : Module.Dual (ZMod 2) (OuterCyclic.Space n)) :
    innerDualRepresentation d x a q = (d.representation a.val (0,q)).2 := by
  rw [inner_action, naturalDualRepresentation_apply]
  rfl

private theorem commutator_comp_surjective {A B W : Type*} [Group A] [Group B]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) B W)
    (e : A →* B) (he : Function.Surjective e) :
    Representation.Coinvariants.ker (ρ.comp e) = Representation.Coinvariants.ker ρ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    exact Representation.Coinvariants.sub_mem_ker (ρ := ρ) (e a) v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨b,v⟩,rfl⟩
    obtain ⟨a,rfl⟩ := he b
    exact Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp e) a v

/-- [X,C_L(x)] = X for the original representation. -/
theorem inner_natural_commutator {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    Representation.Coinvariants.ker (innerNaturalRepresentation d x) = ⊤ := by
  rw [innerNaturalRepresentation, commutator_comp_surjective _ _ (innerEquivPoint d x).surjective]
  exact point_natural_commutator (by simpa only [OuterCyclic.Space, Module.finrank_pi,
    Fintype.card_fin] using (show 3 ≤ n by omega)) hx

/-- [X*,C_L(x)] = ann(x) for the original representation. -/
theorem inner_dual_commutator {n : ℕ} (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    Representation.Coinvariants.ker (innerDualRepresentation d x) = annihilator x := by
  rw [innerDualRepresentation, commutator_comp_surjective _ _ (innerEquivPoint d x).surjective]
  exact point_dual_commutator hx

end BinaryNaturalDual.VectorStabilizers.Pure
