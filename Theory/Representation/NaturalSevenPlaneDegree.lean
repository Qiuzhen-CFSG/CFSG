module
public import Theory.Representation.BinarySevenPlaneDegree
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic

/-!
# Binary degree for a natural seven-plane extension

Suppose a normal subgroup N is identified with the additive F₇-plane and
G/N with SL₂(7), with the literal natural conjugation action. Lift two
specified quaternion matrices through the quotient and transport their
coordinates through the prime-field isomorphism. This constructs the
marked seven-plane required by the binary character-orbit bound, so every
faithful binary representation of G has dimension at least twenty-four.
No splitting of G over N is assumed.

Source application: Aschbacher–Smith, original 12.2.25, printed p.805,
the SL₂(7)/E₄₉ alternative, with the natural-action clause of A.3.6.
-/

public noncomputable section
open Subgroup Matrix
namespace QuaternionSevenPlane
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def firstMatrix : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) :=
  ⟨!![0,4;5,0], by decide⟩
private def secondMatrix : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) :=
  ⟨!![2,5;6,5], by decide⟩

/-- Construct the two quaternion conjugations from the original quotient action. -/
theorem exists_data_of_natural_action
    {G F : Type*} [Group G] [Field F] [Finite F]
    (N : Subgroup G) [N.Normal] (hF : Nat.card F = 7)
    (v : N ≃* Multiplicative (Fin 2 → F))
    (ρ : (G ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hv : ∀ (g : G) (x : N),
      v ⟨g * x * g⁻¹, (inferInstance : N.Normal).conj_mem x x.property g⟩ =
        Multiplicative.ofAdd (Matrix.mulVec (ρ (QuotientGroup.mk' N g)).val
          (Multiplicative.toAdd (v x)))) : Nonempty (Data G) := by
  let := Fintype.ofFinite F
  let e : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [← Nat.card_eq_fintype_card] using hF)
  let c : Multiplicative Plane →* Multiplicative (Fin 2 → F) := {
    toFun z := Multiplicative.ofAdd ![e z.toAdd.1,e z.toAdd.2]
    map_one' := by ext i; fin_cases i <;> simp
    map_mul' x y := by ext i; fin_cases i <;> simp }
  have hc : Function.Injective c := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · exact e.injective (congrArg (fun z : Multiplicative (Fin 2 → F) => z.toAdd 0) hxy)
    · exact e.injective (congrArg (fun z : Multiplicative (Fin 2 → F) => z.toAdd 1) hxy)
  let a := Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective N (ρ.symm (a firstMatrix))
  obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective N (ρ.symm (a secondMatrix))
  let b : Multiplicative Plane →* G := N.subtype.comp (v.symm.toMonoidHom.comp c)
  have hb : Function.Injective b := N.subtype_injective.comp (v.symm.injective.comp hc)
  refine ⟨⟨b,hb,g,k,?_,?_⟩⟩
  · intro z
    have he := hv g (v.symm (c (Multiplicative.ofAdd z)))
    rw [hg,ρ.apply_symm_apply,v.apply_symm_apply] at he
    have hz : Matrix.mulVec (a firstMatrix).val (c (Multiplicative.ofAdd z)).toAdd =
        (c (Multiplicative.ofAdd (firstMap z))).toAdd := by
      change Matrix.mulVec (firstMatrix.val.map e) _ = _
      funext i
      fin_cases i <;> simp [firstMatrix,c,firstMap,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    rw [hz] at he
    exact congrArg (fun x : N => (x : G)) (v.injective (he.trans (v.apply_symm_apply _).symm))
  · intro z
    have he := hv k (v.symm (c (Multiplicative.ofAdd z)))
    rw [hk,ρ.apply_symm_apply,v.apply_symm_apply] at he
    have hz : Matrix.mulVec (a secondMatrix).val (c (Multiplicative.ofAdd z)).toAdd =
        (c (Multiplicative.ofAdd (secondMap z))).toAdd := by
      change Matrix.mulVec (secondMatrix.val.map e) _ = _
      funext i
      fin_cases i <;> simp [secondMatrix,c,secondMap,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    rw [hz] at he
    exact congrArg (fun x : N => (x : G)) (v.injective (he.trans (v.apply_symm_apply _).symm))
end QuaternionSevenPlane

namespace Representation.NaturalSevenPlaneDegree
/-- The literal natural seven-plane extension has no faithful binary module
of dimension less than twenty-four, whether or not the extension splits. -/
theorem finrank_ge
    {G F M : Type*} [Group G] [Field F] [Finite F]
    [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (N : Subgroup G) [N.Normal] (hF : Nat.card F = 7)
    (v : N ≃* Multiplicative (Fin 2 → F))
    (ρ : (G ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hv : ∀ (g : G) (x : N),
      v ⟨g * x * g⁻¹, (inferInstance : N.Normal).conj_mem x x.property g⟩ =
        Multiplicative.ofAdd (Matrix.mulVec (ρ (QuotientGroup.mk' N g)).val
          (Multiplicative.toAdd (v x))))
    (σ : Representation (ZMod 2) G M) (hσ : Function.Injective σ) :
    24 ≤ Module.finrank (ZMod 2) M := by
  obtain ⟨a⟩ := QuaternionSevenPlane.exists_data_of_natural_action N hF v ρ hv
  exact BinarySevenPlaneDegree.finrank_ge σ hσ a
end Representation.NaturalSevenPlaneDegree
