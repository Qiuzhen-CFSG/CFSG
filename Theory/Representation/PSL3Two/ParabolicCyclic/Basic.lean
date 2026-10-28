module

public import Theory.Representation.PSL3Two.FanoQuotients

/-!
# Cyclic orbit maps and the marked line parabolic

A fixed cyclic vector gives a surjection from a transitive permutation
module, with the specified basis vector mapping to the generator. This
construction is applied to the twenty-one actual Fano flags. Cyclic generation
also proves finite dimensionality, without adding it to the input assumptions.
The marked line parabolic is the union of three Borel cosets, represented by
powers of an explicit element of order three.

These are the orbit-map and local group ingredients for Aschbacher–Smith,
H.5.5 and H.6.5, printed pp.386 and 388 of the 1 March 2004 manuscript.
-/

@[expose] public section

open Representation Matrix
namespace BinaryLinearThree.ParabolicCyclic

section General
variable {G M : Type*} [_root_.Group G] [AddCommGroup M] [Module (ZMod 2) M]

/-- Binary linear span of the orbit under the specified subgroup. -/
def orbitSpan (ρ : Representation (ZMod 2) G M) (P : Subgroup G) (m : M) :
    Submodule (ZMod 2) M :=
  Submodule.span (ZMod 2) {v | ∃ p ∈ P, ρ p m = v}

theorem mem_orbitSpan (ρ : Representation (ZMod 2) G M) (P : Subgroup G) (m : M) :
    m ∈ orbitSpan ρ P m := by
  exact Submodule.subset_span ⟨1, P.one_mem, by simp⟩

theorem orbit_mem (ρ : Representation (ZMod 2) G M) (P : Subgroup G)
    (m : M) (g : G) (hg : g ∈ P) : ρ g m ∈ orbitSpan ρ P m :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem orbitSpan_stable (ρ : Representation (ZMod 2) G M) (P : Subgroup G)
    (m : M) (g : G) (hg : g ∈ P) (v : M) (hv : v ∈ orbitSpan ρ P m) :
    ρ g v ∈ orbitSpan ρ P m := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with ⟨p,hp,rfl⟩
    exact Submodule.subset_span ⟨g*p, P.mul_mem hg hp, by
      simp only [map_mul, Module.End.mul_apply]⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using (orbitSpan ρ P m).add_mem ihx ihy
  | smul a v hv ih => simpa only [map_smul] using (orbitSpan ρ P m).smul_mem a ih

/-- A cyclic module for a finite group is finite dimensional. -/
theorem finiteDimensional_of_cyclic [Finite G] (ρ : Representation (ZMod 2) G M)
    (m : M) (hgen : orbitSpan ρ ⊤ m = ⊤) : FiniteDimensional (ZMod 2) M := by
  have hr : {v | ∃ g ∈ (⊤ : Subgroup G), ρ g m = v} = Set.range (fun g => ρ g m) := by
    ext v
    simp
  have hf := FiniteDimensional.span_of_finite (K := ZMod 2)
    (Set.finite_range (fun g => ρ g m))
  rw [← hr, ← orbitSpan, hgen] at hf
  exact Module.Finite.of_injective (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) M) ≃ₗ[ZMod 2] M).symm.toLinearMap
    (Submodule.topEquiv.symm.injective)

theorem intertwiner_eq_zero_of_cyclic
    {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    {ρ : Representation (ZMod 2) G M} {σ : Representation (ZMod 2) G N}
    (m : M) (hgen : orbitSpan ρ ⊤ m = ⊤)
    (f : ρ.IntertwiningMap σ) (hm : f m = 0) : f = 0 := by
  have hle : orbitSpan ρ ⊤ m ≤ LinearMap.ker f.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, rfl⟩
    change f (ρ g m) = 0
    rw [f.isIntertwining, hm, map_zero]
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact hle (by rw [hgen]; trivial)

/-- The orbit map from a fixed cyclic generator extends to a surjective intertwiner. -/
theorem cyclic_permutation_quotient
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (τ : G →* Equiv.Perm Ω) (o : Ω) (H : Subgroup G)
    (hstab : ∀ g : G, g ∈ H ↔ τ g o = o)
    (htrans : ∀ x : Ω, ∃ g : G, τ g o = x)
    (ρ : Representation (ZMod 2) G M) (m : M)
    (hfixed : ∀ g ∈ H, ρ g m = m) (hgen : orbitSpan ρ ⊤ m = ⊤) :
    ∃ f : Representation.IntertwiningMap ((BinaryPermutation.representation Ω).comp τ) ρ,
      Function.Surjective f ∧ f (Pi.single o 1) = m := by
  classical
  let lift (x : Ω) : G := Classical.choose (htrans x)
  have hlift (x : Ω) : τ (lift x) o = x := Classical.choose_spec (htrans x)
  let value (x : Ω) : M := ρ (lift x) m
  have hvalue (g : G) (x : Ω) (hg : τ g o = x) : value x = ρ g m := by
    have hh : (lift x)⁻¹ * g ∈ H := by
      rw [hstab, map_mul, map_inv]
      change (τ (lift x)).symm (τ g o) = o
      rw [hg]
      apply (τ (lift x)).injective
      simpa only [Equiv.apply_symm_apply] using (hlift x).symm
    have he := congrArg (ρ (lift x)) (hfixed _ hh)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he
    exact he.symm
  have hvalue_o : value o = m := by simpa using hvalue 1 o (by simp)
  have hvalue_act (g : G) (x : Ω) : value (τ g x) = ρ g (value x) := by
    have hx : τ (g * lift x) o = τ g x := by
      rw [map_mul]
      change τ g (τ (lift x) o) = τ g x
      rw [hlift]
    rw [hvalue (g * lift x) _ hx, map_mul]
    rfl
  let f : Representation.IntertwiningMap ((BinaryPermutation.representation Ω).comp τ) ρ := {
    toLinearMap := {
      toFun := fun a => ∑ x : Ω, a x • value x
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ x : Ω, a ((τ g).symm x) • value x) =
        ρ g (∑ x : Ω, a x • value x)
      rw [map_sum]
      simp only [map_smul, ← hvalue_act]
      exact (Equiv.sum_comp (τ g)
        (fun x => a ((τ g).symm x) • value x)).symm.trans (by simp) }
  have hf (x : Ω) : f (Pi.single x 1) = value x := by
    change (∑ y : Ω, (Pi.single x (1 : ZMod 2) : Ω → ZMod 2) y • value y) = value x
    simp
  refine ⟨f, ?_, (hf o).trans hvalue_o⟩
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, _, rfl⟩
  refine ⟨Pi.single (τ g o) 1, ?_⟩
  exact (hf _).trans (hvalue g _ rfl)
end General

open FanoDecomposition
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- The five actual representation equivalences asserted in H.6.5. -/
def Alternatives (ρ : Representation (ZMod 2) Group M) : Prop :=
  Nonempty (ρ.Equiv W) ∨ Nonempty (ρ.Equiv U₂) ∨ Nonempty (ρ.Equiv S) ∨
    Nonempty (ρ.Equiv (W.prod S)) ∨ Nonempty (ρ.Equiv (U₂.prod S))

/-- The actual flag permutation module surjects onto a Borel-fixed cyclic module. -/
theorem flag_quotient (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (hgen : orbitSpan ρ ⊤ m = ⊤) :
    ∃ f : flagRepresentation.IntertwiningMap ρ,
      Function.Surjective f ∧ f (Pi.single markedFlag 1) = m := by
  apply cyclic_permutation_quotient flagPerm markedFlag Matrix.PSL3Two.borelSL
    _ markedFlag_reachable ρ m hfixed hgen
  intro g
  rw [← markedFlag_stabilizer]
  rfl

/-- The element cycling the three nonzero points on the marked line. -/
def lineCycle : Group := ⟨!![0,1,0;1,1,0;0,0,1], by decide⟩

theorem lineCycle_cube : lineCycle ^ 3 = 1 := by decide

theorem lineCycle_mem : lineCycle ∈ Matrix.PSL3Two.lineParabolicSL := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Three Borel cosets exhaust the marked line parabolic. -/
theorem line_cosets : ∀ g : Group, g ∈ Matrix.PSL3Two.lineParabolicSL →
    ∃ i : Fin 3, (lineCycle ^ (i : ℕ))⁻¹ * g ∈ Matrix.PSL3Two.borelSL := by
  simp only [Matrix.PSL3Two.mem_lineParabolicSL_iff, Matrix.PSL3Two.mem_borelSL_iff]
  decide +kernel

end BinaryLinearThree.ParabolicCyclic
