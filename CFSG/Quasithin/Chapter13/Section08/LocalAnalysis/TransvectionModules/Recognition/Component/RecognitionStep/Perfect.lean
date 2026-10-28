module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Displacement
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.GroupTheory.IsPerfect
/-!
# Perfect actors and displacement restrictions

If a perfect group acts trivially on E/W, then [E,A]=[W,A]. Modulo
[W,A], the displacement maps E → W/[W,A] form a homomorphism from A
to an abelian group, and therefore vanish. This identifies the component's
commutator space on the restricted displacement module with its commutator
space on the original source module, without assuming they are equal.

Source: the perfect-component restriction in the application of G.6.4 to
13.8.5, Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.947.
-/

@[expose] public section

open Representation Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- A perfect actor has the same commutator space on a central-quotient submodule. -/
theorem perfect_commutator_restriction [Group.IsPerfect A]
    (ρ : Representation (ZMod 2) A E) (S : Subrepresentation ρ)
    (hd : ∀ a v, ρ a v - v ∈ S) :
    Coinvariants.ker ρ = (Coinvariants.ker S.toRepresentation).map S.toSubmodule.subtype := by
  let δ (a : A) : E →ₗ[ZMod 2] S.toSubmodule := (ρ a - LinearMap.id).codRestrict S.toSubmodule (hd a)
  let q := Coinvariants.mk S.toRepresentation
  have hadd (a b : A) : q.comp (δ (a * b)) = q.comp (δ a) + q.comp (δ b) := by
    ext v
    have he : δ (a * b) v = δ a v + S.toRepresentation a (δ b v) := by
      apply Subtype.ext
      change ρ (a * b) v - v = (ρ a v - v) + ρ a (ρ b v - v)
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
    change q (δ (a * b) v) = q (δ a v) + q (δ b v)
    rw [he, map_add, Coinvariants.mk_self_apply]
  let f : A →* Multiplicative (E →ₗ[ZMod 2] Coinvariants S.toRepresentation) :=
    { toFun a := Multiplicative.ofAdd (q.comp (δ a))
      map_one' := by
        apply LinearMap.ext
        intro v
        change q (δ 1 v) = 0
        have hz : δ 1 v = 0 := by
          apply Subtype.ext
          change ρ 1 v - v = 0
          simp
        rw [hz, map_zero]
      map_mul' a b := hadd a b }
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hf (a : A) : f a = 1 := congrArg Subtype.val
    (Subsingleton.elim (⟨f a, a, rfl⟩ : f.range) 1)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩, rfl⟩
    have hz : q (δ a v) = 0 := congrArg (fun k => k.toAdd v) (hf a)
    exact ⟨δ a v, (Coinvariants.mk_eq_zero _).mp hz, rfl⟩
  · rintro _ ⟨v,hv,rfl⟩
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨a,w⟩, rfl⟩ := hv
      exact Coinvariants.sub_mem_ker a (w : E)
    | zero => exact (Coinvariants.ker ρ).zero_mem
    | add v w _ _ hv hw => exact (Coinvariants.ker ρ).add_mem hv hw
    | smul c v _ hv => exact (Coinvariants.ker ρ).smul_mem c hv
/-- The subgroup-displacement convention agrees with the coinvariant kernel
of the restriction to that subgroup. -/
theorem subspaceCommutator_top_eq_coinvariants
    (ρ : Representation (ZMod 2) A E) (C : Subgroup A) :
    subspaceCommutator ρ ⊤ C = Coinvariants.ker (ρ.comp C.subtype) := by
  unfold subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨c, hc, w, _, rfl⟩
    exact ⟨(⟨c, hc⟩, w), rfl⟩
  · rintro ⟨⟨c, w⟩, rfl⟩
    exact ⟨c, c.property, w, Submodule.mem_top, rfl⟩

/-- A perfect subgroup's actual displacement space is unchanged after
restriction to an invariant subspace with trivial quotient action. -/
theorem perfect_subspaceCommutator_restriction
    (ρ : Representation (ZMod 2) A E) (S : Subrepresentation ρ)
    (C : Subgroup A) [Group.IsPerfect C]
    (hd : ∀ (c : C) v, ρ c v - v ∈ S) :
    subspaceCommutator ρ ⊤ C =
      (subspaceCommutator S.toRepresentation ⊤ C).map S.toSubmodule.subtype := by
  let R : Subrepresentation (ρ.comp C.subtype) :=
    ⟨S.toSubmodule, fun c => S.apply_mem_toSubmodule c⟩
  rw [subspaceCommutator_top_eq_coinvariants, subspaceCommutator_top_eq_coinvariants]
  exact perfect_commutator_restriction (ρ.comp C.subtype) R hd

/-- Apply the perfect restriction to the displacement module constructed for G.6.1. -/
theorem displacement_perfect_commutator
    (ρ : Representation (ZMod 2) A E) (t : A)
    (hgen : normalClosure ({t} : Set A) = ⊤)
    (C : Subgroup A) [Group.IsPerfect C] :
    subspaceCommutator ρ ⊤ C =
      (subspaceCommutator (displacementRepresentation ρ t).toRepresentation ⊤ C).map
        (displacementOrbit ρ t).subtype :=
  perfect_subspaceCommutator_restriction ρ (displacementRepresentation ρ t) C
    (fun c v => displacement_mem_of_normalClosure_eq_top ρ t hgen c v)

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

end
