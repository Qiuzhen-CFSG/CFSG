module

public import Theory.GroupTheory.OddKernelInvolutionConjugacy

/-!
# Involution centralizers through an odd kernel

An involution centralizer maps onto the centralizer of its image under a
surjection with odd kernel. Lift a centralizing element, then correct its
conjugate of the involution by the odd-kernel conjugacy theorem. The corrected
lift has the same image and centralizes the original involution.

This retains the literal quotient map used for the full J₄ component in
Aschbacher--Smith 4.4.3, printed p.623.
-/

public section
open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H]

/-- Restrict a homomorphism to the centralizer of the marked element. -/
@[expose] def elementCentralizerMap (f : G →* H) (z : G) :
    centralizer ({z} : Set G) →* centralizer ({f z} : Set H) :=
  (f.comp (centralizer ({z} : Set G)).subtype).codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    change f (x : G) * f z = f z * f (x : G)
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp x.property))

@[simp] theorem elementCentralizerMap_coe (f : G →* H) (z : G)
    (x : centralizer ({z} : Set G)) : (f.elementCentralizerMap z x : H) = f x := rfl

theorem elementCentralizerMap_ker (f : G →* H) (z : G) :
    (f.elementCentralizerMap z).ker = f.ker.subgroupOf (centralizer ({z} : Set G)) := by
  ext x
  exact Subtype.ext_iff

/-- Odd-kernel correction makes the literal centralizer map surjective. -/
theorem elementCentralizerMap_surjective_of_odd_kernel [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (hk : Nat.Coprime 2 (Nat.card f.ker)) (z : G) (hz : orderOf z = 2) :
    Function.Surjective (f.elementCentralizerMap z) := by
  intro y
  obtain ⟨x,hx⟩ := hf y
  have he : f (x * z * x⁻¹) = f z := by
    rw [map_mul,map_mul,map_inv,hx]
    rw [mem_centralizer_singleton_iff.mp y.property,mul_inv_cancel_right]
  obtain ⟨k,hkz⟩ := involutions_same_image_conj_ker f hk
    (((MulAut.conj x).orderOf_eq z).trans hz) hz he
  have hc : (k : G) * x ∈ centralizer ({z} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      ((k : G) * x) * z * ((k : G) * x)⁻¹ =
          (k : G) * (x * z * x⁻¹) * (k : G)⁻¹ := by group
      _ = z := hkz
  refine ⟨⟨(k : G) * x,hc⟩,Subtype.ext ?_⟩
  change f ((k : G) * x) = (y : H)
  rw [map_mul,k.property,one_mul,hx]

end MonoidHom
