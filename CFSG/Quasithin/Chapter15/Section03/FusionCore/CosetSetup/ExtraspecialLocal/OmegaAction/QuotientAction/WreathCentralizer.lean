module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.Setup

/-!
# Faithfulness detected by the orthogonal two-residual

In the literal binary orthogonal wreath model, an actor centralizing every
cube-trivial element is itself cube-trivial. A kernel-checked finite calculation
proves this assertion. Every element of order three belongs to O², so a
two-element centralizing O² is trivial by coprimality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the natural
orthogonal structure on printed pp.1121–1122, used on p.1143.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal
private instance : DecidableEq OrthogonalActor :=
  fun a b => decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    RegularWreathProduct.ext_iff.symm
private instance : Fintype OrthogonalActor :=
  Fintype.ofEquiv ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
    (RegularWreathProduct.equivProd _ _).symm
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem centralizer_cube : ∀ a : OrthogonalActor,
    (∀ b : OrthogonalActor, b ^ 3 = 1 → a * b = b * a) → a ^ 3 = 1 := by
  decide +kernel

/-- Two-elements centralizing the orthogonal two-residual are trivial. -/
theorem orthogonal_two_centralizer (P : Subgroup OrthogonalActor)
    (hP : IsPGroup 2 P) (a : P)
    (ha : (a : OrthogonalActor) ∈ centralizer
      (twoResidualAmbient (⊤ : Subgroup OrthogonalActor) : Set OrthogonalActor)) :
    a = 1 := by
  have h3 : (a : OrthogonalActor) ^ 3 = 1 := by
    apply centralizer_cube
    intro b hb
    by_cases h1 : b = 1
    · simp [h1]
    have ho : orderOf b = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hb) |>.resolve_left
        (fun h => h1 (orderOf_eq_one_iff.mp h))
    exact (ha b (theta_le_twoResidual _ (Subgroup.subset_closure ⟨mem_top b, ho⟩))).symm
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hP.orderOf_coprime (by decide : Nat.Coprime 2 3) a)
    dvd_rfl (orderOf_dvd_of_pow_eq_one (show a ^ 3 = 1 from Subtype.ext h3))
end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
