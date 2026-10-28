module

public import Theory.Representation.PSL3Two.SingerRestriction
public import Theory.Representation.PSL3Two.SingerRestriction.FiveSpace.Normalizer

/-!
# Five-dimensional restriction of the actual binary Steinberg module

Averaging gives the direct sum of the Singer fixed plane and the literal
three-dimensional displacement span. Prime-order orbit counting makes the
Singer action transitive on its seven nonzero vectors. The checked canonical
normalizer action, transported by conjugacy, preserves the moved part and
therefore the five-space. This proves precisely the module restriction used
in J.2.3; construction of the source centralizer subspace is separate.

Source: Aschbacher–Smith, J.2.3, printed pp.433–434 (PDF pp.444–445).
-/

public section

open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
open Subgroup
namespace BinaryLinearThree.SingerRestriction.FiveSpace
noncomputable local instance : AddCommGroup Steinberg := inferInstance
noncomputable local instance : Module (ZMod 2) Steinberg := inferInstance

private theorem map_eq_of_mem (A : Submodule (ZMod 2) Steinberg) (g : Group)
    (h : ∀ v ∈ A, S g v ∈ A) : A.map (S g) = A := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v,hv,rfl⟩
    exact h v hv
  · exact (Submodule.equivMapOfInjective (S g) (S.apply_bijective g).injective A).finrank_eq.symm

private theorem fixed_map (H : Subgroup Group) (g : Group) (hg : g ∈ normalizer H) :
    (fixedSpace S H).map (S g) = fixedSpace S H := by
  apply map_eq_of_mem
  intro v hv
  rw [← mem_normalizer_iff_map_conj_eq.mp hg]
  intro k
  obtain ⟨a, ha, heq⟩ := k.property
  change S (k : Group) (S g v) = S g v
  rw [← heq]
  exact (conjugate_apply g a v).trans (congrArg (S g) (hv ⟨a, ha⟩))

/-- The whole Singer normalizer preserves both the five-space and its moving
three-space. In particular the source cubic subgroup preserves them. -/
theorem normalizer_maps (H : Subgroup Group) (hH : Nat.card H = 7)
    (A : Submodule (ZMod 2) Steinberg) (hA5 : Module.finrank (ZMod 2) A = 5)
    (hFA : fixedSpace S H ≤ A) (hA : ∀ h ∈ H, ∀ a ∈ A, S h a ∈ A)
    (g : Group) (hg : g ∈ normalizer H) :
    A.map (S g) = A ∧ (displacementSpan S H A).map (S g) = displacementSpan S H A := by
  have hd := decomposition H hH A hA5 hFA hA
  have hm : (displacementSpan S H A).map (S g) = displacementSpan S H A := by
    apply map_eq_of_mem
    exact normalizer_mem H hH _ (moved_mem H A hA) hd.2.2
      (transitive H hH A hA5 hFA hA) g hg
  refine ⟨?_,hm⟩
  calc
    A.map (S g) = (fixedSpace S H ⊔ displacementSpan S H A).map (S g) := congrArg _ hd.2.1
    _ = fixedSpace S H ⊔ displacementSpan S H A := by
      rw [Submodule.map_sup, fixed_map H g hg, hm]
    _ = A := hd.2.1.symm

/-- The five-dimensional restriction required in J.2.3. Every conclusion is
proved from dimension, Singer invariance and containment of the fixed plane. -/
theorem restriction (H D : Subgroup Group) (hH : Nat.card H = 7)
    (_hD : Nat.card D = 3) (hDH : D ≤ normalizer H)
    (A : Submodule (ZMod 2) Steinberg) (hA5 : Module.finrank (ZMod 2) A = 5)
    (hFA : fixedSpace S H ≤ A) (hA : ∀ h ∈ H, ∀ a ∈ A, S h a ∈ A) :
    let M := displacementSpan S H A
    Module.finrank (ZMod 2) M = 3 ∧
    A = fixedSpace S H ⊔ M ∧ fixedSpace S H ⊓ M = ⊥ ∧
    (∀ g ∈ D, A.map (S g) = A ∧ M.map (S g) = M) ∧
    (∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ H, S h v = w) := by
  have hd := decomposition H hH A hA5 hFA hA
  exact ⟨hd.1, hd.2.1, hd.2.2,
    fun g hg => normalizer_maps H hH A hA5 hFA hA g (hDH hg),
    transitive H hH A hA5 hFA hA⟩
end BinaryLinearThree.SingerRestriction.FiveSpace
