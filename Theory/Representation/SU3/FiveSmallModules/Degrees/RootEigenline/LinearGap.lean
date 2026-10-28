module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.Contracts
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.LinearGap.DualWeights
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.LinearGap.RootCoordinates
public import Theory.Representation.InvariantsBaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The linear-root gap for SU₃(5)

On the center-fixed space, the root action factors through the additive first
coordinate. A nontrivial occurring character has eight distinct torus pullbacks.
Their independent weight spaces contradict dimension below eight. Thus the
center-fixed space is root-fixed over the algebraic closure. Invariant-space
base change and equality of dimensions descend this conclusion to the original
finite characteristic-two field.

The proof uses the actual special-unitary root map and its embedded center.
It imposes no condition on the kernel or irreducibility of the representation.

Source: the root-group calculation for Guralnick–Malle, *Classification of
2F-modules I*, Proposition 4.3, p.10; Aschbacher–Smith K.2, printed p.453.
-/

public section

universe u v

open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.OddPrimeSylow.NormalizedOuter HermitianForm.BorelTorus
namespace Representation.SU3.FiveSmallModules.Degrees.RootEigenline

open LinearGap

/-- The center-fixed space of dimension below eight is root-fixed over a
splitting field, without any assumption on the kernel of the representation. -/
theorem root_linear_gap_of_isAlgClosed
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {E U : Type*} [Field E] [IsAlgClosed E] [CharP E 2]
    [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (τ : Representation E (standardGroup J) U)
    (hdim : Module.finrank E (invariants (τ.comp (standardRootCenter J).subtype)) < 8) :
    invariants (τ.comp (standardRoot J).subtype) =
      invariants (τ.comp (standardRootCenter J).subtype) := by
  let J' := FormTransport.standardForm J
  have hJ' : J'.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : CharP F 5 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have h2 : (2 : F) ≠ 0 := (CharP.cast_eq_zero_iff F 5 2).not.mpr (by decide)
  obtain ⟨k, hk⟩ := exists_eight_torus_powers hc
  have horder : (Nat.card (Multiplicative F) : E) ≠ 0 := by
    rw [Nat.card_congr Multiplicative.toAdd, hc]
    exact (CharP.cast_eq_zero_iff E 2 25).not.mpr (by decide)
  have hd : Module.finrank E (invariants ((τ.comp (hermitianUnipotentSU J' hJ')).comp
      (Subgroup.center (hermitianUnipotentCoord J')).subtype)) < Nat.card (Fin 8) := by
    rw [center_invariants_eq J' hJ' τ, Nat.card_fin]
    exact hdim
  have he := root_invariants_eq_center_of_scalar_conjugacies τ
    (hermitianUnipotentSU J' hJ') (firstCoordinate J')
    (firstCoordinate_surjective J' h2) (firstCoordinate_ker_le_center J') horder
    (fun i : Fin 8 => ((k ^ i.val : Fˣ) : F) ^ 9) hk
    (fun i => hermitianTorusSU J' hJ' (k ^ i.val))
    (fun i => inverseTorus J' hJ' (k ^ i.val))
    (fun i => inverseTorus_conjugation J' hJ' (k ^ i.val))
    (fun i => firstCoordinate_inverseTorus J' hJ' hconj (k ^ i.val)) hd
  rw [center_invariants_eq J' hJ' τ] at he
  have hr : invariants (τ.comp (hermitianUnipotentSU J' hJ')) =
      invariants (τ.comp (standardRoot J).subtype) := by
    ext v
    constructor
    · intro hv p
      obtain ⟨z, hz⟩ := p.property
      change τ p.val v = v
      rw [← hz]
      exact hv z
    · intro hv z
      exact hv ⟨hermitianUnipotentSU J' hJ' z, ⟨z, rfl⟩⟩
  exact hr.symm.trans he

/-- The linear-root gap over the original characteristic-two coefficient field.
Scalar extension preserves both fixed-space dimensions, so the equality over
the algebraic closure descends by inclusion and equality of dimensions. -/
theorem root_linear_gap_input : RootLinearGapInput.{u, v} := by
  intro F _ _ J hc hconj K _ _ _ U _ _ _ τ hdim
  let E := AlgebraicClosure K
  let τ' := τ.extendScalars E
  have hd (H : Subgroup (standardGroup J)) :
      Module.finrank E (invariants (τ'.comp H.subtype)) =
        Module.finrank K (invariants (τ.comp H.subtype)) :=
    finrank_invariants_extendScalars_eq_of_finite (E := E) (τ.comp H.subtype)
  have he := root_linear_gap_of_isAlgClosed J hc hconj τ'
    (by rw [hd]; exact hdim)
  apply Submodule.eq_of_le_of_finrank_eq
  · intro v hv z
    obtain ⟨p, _, hp⟩ := z.property
    change τ z.val v = v
    rw [← hp]
    exact hv p
  · rw [← hd (standardRoot J), ← hd (standardRootCenter J), he]

end Representation.SU3.FiveSmallModules.Degrees.RootEigenline
