module
public import Theory.Representation.BinaryPermutation.FiveTensorFixedLine
/-!
# Sylow-fixed points in the five-letter binary core

The regular Klein four fixes only the weight-four line. Conjugating it
into an arbitrary Sylow two-subgroup and preserving the quadratic form
shows that every Sylow-fixed point is singular.

Source: Aschbacher–Smith, 13.7.6(3), printed p.939, degree-five exclusion.
-/
@[expose] public section
open BinaryPermutation Subgroup
namespace BinaryPermutation.FiveSylowSingular
open CubicFixedSpace.Five
private theorem klein_fixed_singular (v : core (Fin 5))
    (h₁ : coreRepresentation (Fin 5) first.val v = v)
    (h₂ : coreRepresentation (Fin 5) second.val v = v) : FiveGeometry.form v = 0 := by
  have h : ∀ x : Full (Fin 5), (∑ i,x i) = 0 →
      representation (Fin 5) first.val x = x →
      representation (Fin 5) second.val x = x →
      x = 0 ∨ (Finset.univ.filter fun i => x i ≠ 0).card = 4 := by decide
  rw [FiveGeometry.singular_iff]
  rcases h v.val v.property (congrArg Subtype.val h₁) (congrArg Subtype.val h₂) with hz | hw
  · exact Or.inl (Subtype.ext hz)
  · exact Or.inr hw
/-- Every vector fixed by a Sylow two-subgroup of the literal A5 actor is singular. -/
theorem fixed_singular (P : Sylow 2 (alternatingGroup (Fin 5)))
    (v : core (Fin 5))
    (hv : ∀ g ∈ P, alternatingCoreRepresentation (Fin 5) g v = v) :
    FiveGeometry.form v = 0 := by
  obtain ⟨Q,hQ⟩ := klein_isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) Q P
  have hP : (Q : Subgroup _).map (MulAut.conj g).toMonoidHom = P := by
    rw [← hg]
    rfl
  let r := alternatingCoreRepresentation (Fin 5)
  have hh (a : alternatingGroup (Fin 5)) (ha : a ∈ klein) : r a (r g⁻¹ v) = r g⁻¹ v := by
    have hm : g * a * g⁻¹ ∈ P := by
      change g * a * g⁻¹ ∈ (P : Subgroup (alternatingGroup (Fin 5)))
      rw [←hP]
      exact ⟨a,hQ ha,rfl⟩
    have hh : r (g * a * g⁻¹) v = v := hv _ hm
    have he := congrArg (r g⁻¹) hh
    simpa only [← Module.End.mul_apply,← map_mul,mul_assoc,inv_mul_cancel_left] using he
  have hs := klein_fixed_singular (r g⁻¹ v) (hh first first_mem) (hh second second_mem)
  have ht := FiveTensorFixedLine.singular_permute g.val (r g⁻¹ v) hs
  have hi : coreRepresentation (Fin 5) g.val (r g⁻¹ v) = v := by
    change r g (r g⁻¹ v) = v
    rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  rwa [hi] at ht
end BinaryPermutation.FiveSylowSingular
