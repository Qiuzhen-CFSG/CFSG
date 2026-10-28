module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Faithfulness of a local extension action

Let `B` be normal in `Y`, let `mu : B →* G` be injective, and let `rho`
act on `G` compatibly with conjugation on `B`. If the centralizer of `B`
in `Y` lies in a subgroup `A` on which `rho` is faithful, then `rho` is
faithful on all of `Y`.

A kernel element fixes `mu(B)`, hence centralizes `B` by injectivity of
`mu`. It therefore lies in `A`, where faithfulness finishes the argument.

This is the additional local kernel argument needed in applications of
Aschbacher–Smith, *The Classification of Quasithin Groups*, F.2.11 to
F.4.23(5). The centralizer-containment hypothesis is explicit; it is not
claimed to follow from the hypotheses printed in F.2.11.
-/

namespace Theory.GroupTheory

public theorem automorphismHom_injective_of_local_centralizer
    {Y G : Type*} [Group Y] [Group G]
    (A B : Subgroup Y) [B.Normal]
    (mu : B →* G) (hmu : Function.Injective mu)
    (rho : Y →* MulAut G)
    (hcompat : ∀ (y : Y) (b : B),
      mu (MulAut.conjNormal y b) = rho y (mu b))
    (hcentralizer : Subgroup.centralizer (B : Set Y) ≤ A)
    (hA : Function.Injective (rho.comp A.subtype)) :
    Function.Injective rho := by
  apply rho.ker_eq_bot_iff.mp
  apply bot_unique
  intro y hy
  have hry : rho y = 1 := hy
  have hyC : y ∈ Subgroup.centralizer (B : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hfixed : MulAut.conjNormal y (⟨b, hb⟩ : B) = ⟨b, hb⟩ := by
      apply hmu
      rw [hcompat, hry]
      rfl
    have hv : y * b * y⁻¹ = b := congrArg Subtype.val hfixed
    have hv' := congrArg (fun z : Y => z * y) hv
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hv'.symm
  have hyA := hcentralizer hyC
  have heq : (⟨y, hyA⟩ : A) = 1 := hA (by
    change rho y = rho 1
    simpa using hry)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val heq)

end Theory.GroupTheory
