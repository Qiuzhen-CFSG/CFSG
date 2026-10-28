module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension

/-!
# Actual subgroups in the orthogonal branch of §14.4

These definitions retain D = [U,i]⟨i,z⟩, its base [U,i]⟨z⟩, the residual
K₀ = O²(C_H(i)), and the literal relative normalizer T_D = N_T(D).
The source exponent convention is z^x = x⁻¹zx; the same conjugation is used
for U^x. None of the definitions asserts that the orthogonal branch exists
or that its local calculations have been proved.

Source: Aschbacher–Smith, Lemma 14.4.9, printed pp.1009–1010.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G]

/-- Conjugation in the exponent convention of the source. -/
def conjugateElement (z x : G) : G := (MulAut.conj x⁻¹) z

/-- The subgroup U^x, with the same convention as `conjugateElement`. -/
def conjugateCore (U : Subgroup G) (x : G) : Subgroup G :=
  U.map (MulAut.conj x⁻¹).toMonoidHom

/-- The preimage of the moved space, including the central involution. -/
def liftBase (U : Subgroup G) (z i : G) : Subgroup G :=
  ⁅U, zpowers i⁆ ⊔ zpowers z

/-- The elementary lift to be constructed in the source argument. -/
def centralizerLift (U : Subgroup G) (z i : G) : Subgroup G :=
  ⁅U, zpowers i⁆ ⊔ zpowers i ⊔ zpowers z

/-- The actual two-residual of C_H(i), before proving its diagonal action. -/
def diagonalResidual (H : Subgroup G) (i : G) : Subgroup G :=
  twoResidual (H ⊓ centralizer ({i} : Set G))

/-- The generating group Y = ⟨K₀U,U^x⟩ from the source. -/
def symmetricActor (U : Subgroup G) (z x : G) : Subgroup G :=
  diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ⊔ U ⊔
    conjugateCore U x

/-- The literal N_T(D), viewed in the original ambient group. -/
def localSylow (T D : Subgroup G) : Subgroup G := T ⊓ normalizer (D : Set G)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
