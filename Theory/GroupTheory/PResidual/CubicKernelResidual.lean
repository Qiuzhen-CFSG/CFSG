module
public import Theory.GroupTheory.PResidual.CubicActionKernel
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PResidual.NormalThreeLift

/-!
# A cubic residual in an order-nine action kernel

For a two-perfect group A with |A/O₂(A)| = 9, a nontrivial action in a group
whose order has greatest common divisor three with nine has a cubic kernel
image modulo O₂(A). Taking O² of the literal action kernel preserves that
image, because a group of order three is two-perfect. Normality then identifies
its intrinsic two-core quotient with the same image.

Source application: the subgroup Y_C in Aschbacher–Smith, 14.5.20,
printed p.1019, refs/quasithin.pdf. The original-group application is
LocalReduction.SolvableNineKernel.
-/

public noncomputable section
open Subgroup
namespace MonoidHom

/-- The two-residual of the literal action kernel is a normal cubic lift,
with the same image through the whole two-core kernel. -/
theorem cubic_kernel_residual
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hA : IsPPerfect 2 A) (hne : f ≠ 1)
    (h9 : Nat.card (A ⧸ pCore 2 A) = 9)
    (hB : Nat.gcd 9 (Nat.card B) = 3) :
    let C := (pResidual 2 f.ker).map f.ker.subtype
    C.Normal ∧ IsPPerfect 2 C ∧ C ≤ f.ker ∧
      C.map (QuotientGroup.mk' (pCore 2 A)) =
        f.ker.map (QuotientGroup.mk' (pCore 2 A)) ∧
      Nat.card (C ⧸ pCore 2 C) = 3 := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let C := (pResidual 2 f.ker).map f.ker.subtype
  have hp : IsPPerfect 2 (⊤ : Subgroup A) := hA.of_surjective
    (topEquiv (G := A)).symm.toMonoidHom (topEquiv (G := A)).symm.surjective
  have hout : ¬ (⊤ : Subgroup A) ≤ f.ker := by
    intro ht
    apply hne
    ext x
    exact ht (mem_top x)
  have hc : Nat.card (f.ker.map q) = 3 := f.card_kernel_image_cubic ⊤ hp hout h9 hB
  have hperfect : IsPPerfect 2 (f.ker.map q) := by
    apply (pResidual_eq_top_iff 2 _).mp
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime
      ((show Nat.Coprime 2 3 by decide).of_dvd_right (hc ▸ orderOf_dvd_natCard x))
  have hm : C.map q = f.ker.map q := by
    rw [show C = (pResidual 2 f.ker).map f.ker.subtype from rfl,
      map_embedded_pResidual,(pResidual_eq_top_iff 2 _).mpr hperfect,
      ←MonoidHom.range_eq_map,range_subtype]
  exact ⟨inferInstance,isPPerfect_embedded_pResidual 2 _,map_subtype_le _,hm,
    (Nat.card_congr (coreQuotientEquivImage 2 C).toEquiv).trans (by rw [hm]; exact hc)⟩

end MonoidHom
