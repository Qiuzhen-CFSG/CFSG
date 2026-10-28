module
public import Theory.Representation.BinaryAlternatingFiveExtension.TriangleTranslation
public import Theory.Representation.BinaryPermutation.SevenPointChiefFactor

/-!
# Overgroups of the actual affine A₅ complement

An overgroup of the literal complement cuts out an invariant subspace in
the binary five-point core. Simplicity of that actual module makes the
subspace zero or full, and the semidirect product decomposition gives the
two corresponding overgroups. This supplies the local maximality used to
recover the whole involution centralizer from the source triangle.
-/

public noncomputable section
open Subgroup
namespace BinaryPermutation.AlternatingFiveExtension.TriangleTranslation
open AlternatingFiveBorel

/-- The actual A₅ complement has no proper intermediate overgroup. -/
theorem overgroup_complement_eq_or_top (K : Subgroup Model)
    (hK : (SemidirectProduct.inr : alternatingGroup (Fin 5) →* Model).range ≤ K) :
    K = (SemidirectProduct.inr : alternatingGroup (Fin 5) →* Model).range ∨ K = ⊤ := by
  let S : Submodule (ZMod 2) (core (Fin 5)) := {
    carrier := {v | (SemidirectProduct.inl (Multiplicative.ofAdd v) : Model) ∈ K}
    zero_mem' := K.one_mem
    add_mem' := by
      intro v w hv hw
      change (SemidirectProduct.inl (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : Model) ∈ K
      rw [map_mul]
      exact K.mul_mem hv hw
    smul_mem' := by
      intro c v hv
      change (SemidirectProduct.inl (Multiplicative.ofAdd (c • v)) : Model) ∈ K
      fin_cases c
      · change (SemidirectProduct.inl (Multiplicative.ofAdd ((0 : ZMod 2) • v)) : Model) ∈ K
        rw [zero_smul]
        exact K.one_mem
      · change (SemidirectProduct.inl (Multiplicative.ofAdd ((1 : ZMod 2) • v)) : Model) ∈ K
        rw [one_smul]
        exact hv }
  have hS (g : alternatingGroup (Fin 5)) (v : core (Fin 5)) (hv : v ∈ S) :
      coreRepresentation (Fin 5) g.val v ∈ S := by
    change (SemidirectProduct.inl (action g (Multiplicative.ofAdd v)) : Model) ∈ K
    rw [SemidirectProduct.inl_aut]
    exact K.mul_mem (K.mul_mem (hK ⟨g,rfl⟩) hv) (hK ⟨g⁻¹,rfl⟩)
  have hinl (x : Model) (hx : x ∈ K) : (SemidirectProduct.inl x.left : Model) ∈ K := by
    have hh := K.mul_mem hx (K.inv_mem (hK ⟨x.right,rfl⟩))
    have he : x * (SemidirectProduct.inr x.right)⁻¹ = (SemidirectProduct.inl x.left : Model) :=
      mul_inv_eq_iff_eq_mul.mpr (SemidirectProduct.inl_left_mul_inr_right x).symm
    rwa [he] at hh
  rcases SevenPointChiefFactor.fiveCore_simple S hS with hzero | hfull
  · left
    apply le_antisymm _ hK
    intro x hx
    have hv : x.left.toAdd ∈ S := hinl x hx
    rw [hzero,Submodule.mem_bot] at hv
    have hleft : x.left = 1 := congrArg Multiplicative.ofAdd hv
    refine ⟨x.right,?_⟩
    rw [←SemidirectProduct.inl_left_mul_inr_right x,hleft,map_one,one_mul]
    rfl
  · right
    apply top_unique
    intro x _
    rw [←SemidirectProduct.inl_left_mul_inr_right x]
    apply K.mul_mem _ (hK ⟨x.right,rfl⟩)
    exact show x.left.toAdd ∈ S from hfull ▸ Submodule.mem_top

end BinaryPermutation.AlternatingFiveExtension.TriangleTranslation
