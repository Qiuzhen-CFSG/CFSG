module
public import Theory.Representation.BinaryOffender.QuadraticDisjointSummands

/-!
# Faithfulness on invariant sections

A pointwise section kernel normalizing an actor centralizes that actor when the
actor acts faithfully on the section. This transfers faithfulness to elementary
actors with trivial centralizer intersection. The quadratic disjoint-summand
lemma then makes a section stabilizer trivial.

These are the kernel and stabilizer steps in the constituent argument of
Aschbacher–Smith, *The Classification of Quasithin Groups*, D.3.5–D.3.7.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- A pointwise kernel on a faithful invariant section centralizes its actor.
This does not assume that the section kernel is normal in the ambient group. -/
theorem centralizes_of_fixes_faithful_section (K : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (hfaith : ∀ k ∈ K, (∀ v ∈ I, ρ k v = v) → k = 1)
    {b : D} (hn : b ∈ normalizer (K : Set D))
    (hb : ∀ v ∈ I, ρ b v = v) : b ∈ centralizer (K : Set D) := by
  have hbi (v : V) (hv : v ∈ I) : ρ b⁻¹ v = v := by
    have hh := congrArg (ρ b⁻¹) (hb v hv)
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh.symm
  intro k hk
  have hconj : b*k*b⁻¹ ∈ K := (hn k).mp hk
  have hcom : b*k*b⁻¹*k⁻¹ ∈ K := K.mul_mem hconj (K.inv_mem hk)
  have he : b*k*b⁻¹*k⁻¹ = 1 := hfaith _ hcom (by
    intro v hv
    have hki : ρ k⁻¹ v ∈ I := (hI (K.inv_mem hk) v).2 hv
    simp only [map_mul, Module.End.mul_apply, hbi _ hki]
    have hkiv : ρ k (ρ k⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hkiv, hb v hv])
  have he' : b*k*b⁻¹ = k := mul_inv_eq_one.mp he
  have he'' := congrArg (fun x : D => x*b) he'
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using he''.symm

/-- Faithfulness of the same elementary actor on the component orbit passes
to any invariant section on which that orbit acts faithfully. -/
theorem actor_faithful_on_section (K A : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (hK : ∀ k ∈ K, (∀ v ∈ I, ρ k v = v) → k = 1)
    (hAN : A ≤ normalizer (K : Set D))
    (hA : A ⊓ centralizer (K : Set D) = ⊥) :
    ∀ a ∈ A, (∀ v ∈ I, ρ a v = v) → a = 1 := by
  intro a ha hf
  have hc := centralizes_of_fixes_faithful_section ρ K I hI hK (hAN ha) hf
  exact mem_bot.mp (hA ▸ (show a ∈ A ⊓ centralizer (K : Set D) from ⟨ha,hc⟩))

/-- The stabilizer in a quadratic actor is trivial whenever it moves a
disjoint copy of a section faithful for the whole component orbit. -/
theorem quadratic_stabilizer_eq_one (K A : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (hK : ∀ k ∈ K, (∀ v ∈ I, ρ k v = v) → k = 1)
    (hAN : A ≤ normalizer (K : Set D))
    (hA : A ⊓ centralizer (K : Set D) = ⊥)
    (hq : IsQuadratic ρ A) {a b : D} (ha : a ∈ A) (hb : b ∈ A)
    (hd : Disjoint I (I.map (ρ a))) (hs : b ∈ subspaceStabilizer ρ I) : b = 1 :=
  actor_faithful_on_section ρ K A I hI hK hAN hA b hb
    (quadratic_fixes_disjoint_summand ρ I hq ha hb hd (fun v hv => (hs v).2 hv))

end Representation.BinaryOffender
