module
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.Algebra.Module.ZMod
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# Lifting full coinvariants through a derived kernel

Let Q be a finite normal two-subgroup and let an equivariant elementary quotient
have kernel Q′. If the displacements of a marked subgroup span this quotient,
then Q is its full commutator subgroup. Surjectivity first gives generation
modulo Q′; nilpotent saturation then removes that derived supplement.

The application is the full core cover in Aschbacher–Smith 15.3.23 and15.3.31,
printed pp.1128–1129 and1132. No particular model or simple group is required.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace Representation

variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- A full elementary quotient with derived kernel lifts marked coinvariant generation
in a finite two-group to literal subgroup commutator generation. -/
theorem subgroup_eq_commutator_of_full_coinvariants [Finite G]
    (Q B : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q)
    (actor : G →* A) (ρ : Representation (ZMod 2) A V)
    (f : Q →* Multiplicative V) (hf : Function.Surjective f)
    (hk : f.ker = _root_.commutator Q)
    (ha : ∀ (g : G) (q q' : Q), (q' : G) = g * (q : G) * g⁻¹ →
      (f q').toAdd = ρ (actor g) (f q).toAdd)
    (hgen : Coinvariants.ker (ρ.comp (B.map actor).subtype) = ⊤) :
    Q = ⁅Q,B⁆ := by
  let N : Subgroup (Multiplicative V) := (⁅Q,B⁆.subgroupOf Q).map f
  let U : Submodule (ZMod 2) V := AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm N)
  have hspan : Coinvariants.ker (ρ.comp (B.map actor).subtype) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    obtain ⟨b,hb,hab⟩ := a.property
    obtain ⟨q,hq⟩ := hf (Multiplicative.ofAdd v)
    let q' : Q := ⟨b * (q:G) * b⁻¹, (inferInstance : Q.Normal).conj_mem q q.property b⟩
    change Multiplicative.ofAdd (ρ a.val v - v) ∈ N
    refine mem_map.mpr ⟨q' * q⁻¹, ?_, ?_⟩
    · change b * (q:G) * b⁻¹ * (q:G)⁻¹ ∈ ⁅Q,B⁆
      rw [commutator_comm Q B]
      exact commutator_mem_commutator hb q.property
    · rw [map_mul,map_inv]
      have he : f q' = Multiplicative.ofAdd (ρ (actor b) v) := by
        have hh := ha b q q' rfl
        rw [hq] at hh
        exact congrArg Multiplicative.ofAdd hh
      rw [he,hq,hab]
      exact congrArg Multiplicative.ofAdd (sub_eq_add_neg _ _).symm
  have hN : N = ⊤ := by
    apply top_unique
    intro v _
    exact hspan (hgen ▸ (show v.toAdd ∈ (⊤ : Submodule (ZMod 2) V) from Submodule.mem_top))
  have hcover : Q ≤ ⁅Q,B⁆ ⊔ ⁅Q,Q⁆ := by
    intro q hq
    obtain ⟨n,hn,hfn⟩ := (show f ⟨q,hq⟩ ∈ N from hN ▸ mem_top _)
    have hz : q * (n:G)⁻¹ ∈ ⁅Q,Q⁆ := by
      have hh : (⟨q,hq⟩ : Q) * n⁻¹ ∈ f.ker := by
        change f ((⟨q,hq⟩ : Q) * n⁻¹) = 1
        rw [map_mul,map_inv,hfn,mul_inv_cancel]
      rw [hk] at hh
      rw [← map_subtype_commutator]
      exact mem_map.mpr ⟨_,hh,rfl⟩
    have hh := (⁅Q,B⁆ ⊔ ⁅Q,Q⁆).mul_mem (mem_sup_right hz) (mem_sup_left hn)
    change q * (n:G)⁻¹ * (n:G) ∈ ⁅Q,B⁆ ⊔ ⁅Q,Q⁆ at hh
    simpa only [inv_mul_cancel_right] using hh
  have hle : ⁅Q,B⁆ ≤ Q := commutator_le_left Q B
  apply le_antisymm _ hle
  exact le_of_le_sup_commutator_of_isPGroup Q ⁅Q,B⁆ Q hQ hQ hle
    Q.le_normalizer (normalizer_commutator_ge_left Q B) hcover

end Representation

