module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.ElementaryNormalizer
/-!
# The remaining unitriangular calculations for source Lemma 3.1

Squares lie in the middle sixteen. Commuting with its four coordinate generators
forces membership in it; commuting with four Sylow generators leaves only the
identity and the central root involution. These checks use the 64-element Sylow
model, not enumeration of subgroups of the full block. Finally the centralizer
of that marked involution lies in the point stabilizer, by its natural action
on the translation vector e₀. Construction transports these facts to C_G(z).
Source: Aschbacher, “A 2-local characterization of M12”, Lemma 3.1, p.36.
-/

public section

open Subgroup Matrix.PSL3Two Matrix.PSL3Two.SplitParabolic
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.ConstructionModel
open Unitriangular

theorem square_mem (x : T) : x ^ 2 ∈ A := by
  revert x
  decide +kernel

theorem center_cases (x : T) (hx : x ∈ center T) : x = 1 ∨ x = Unitriangular.z := by
  have h := mem_center_iff.mp hx
  have hc : ∀ x : T, r*x=x*r → q*x=x*q → bit 0*x=x*bit 0 →
      bit 3*x=x*bit 3 → x=1 ∨ x=Unitriangular.z := by decide +kernel
  exact hc x (h r) (h q) (h (bit 0)) (h (bit 3))

theorem centralizer_middle (x : T) (hx : x ∈ centralizer (A : Set T)) : x ∈ A := by
  have hb : ∀ i : Fin 4, bit i ∈ A := by decide +kernel
  have hc : ∀ x : T, bit 0*x=x*bit 0 → bit 1*x=x*bit 1 →
      bit 2*x=x*bit 2 → bit 3*x=x*bit 3 → x ∈ A := by decide +kernel
  exact hc x (hx _ (hb 0)) (hx _ (hb 1)) (hx _ (hb 2)) (hx _ (hb 3))

theorem marked_centralizer_le_point :
    centralizer ({sylowMap Unitriangular.z} : Set Block) ≤ pointPreimage := by
  intro b hb
  have he := mem_centralizer_singleton_iff.mp hb
  have hz : sylowMap Unitriangular.z =
      (SemidirectProduct.inl (Multiplicative.ofAdd ![1,0,0]) : Block) := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      fin_cases i <;> decide +kernel
    · apply Subtype.ext
      decide +kernel
  rw [hz] at he
  have hv := congrArg (fun b : Block => b.left.toAdd) he
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hv
  change b.left.toAdd + b.right.val.mulVec ![1,0,0] =
    ![1,0,0] + b.left.toAdd at hv
  change b.right ∈ pointParabolicSL
  rw [mem_pointParabolicSL_iff]
  constructor
  · have hi := congrFun hv 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hi
  · have hi := congrFun hv 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hi
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.ConstructionModel

end
