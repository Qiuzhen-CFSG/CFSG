module

public import Theory.Representation.BinaryOffender.CodimensionSieve
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Dimensions

/-!
# The six-versus-five contradiction in 13.8.25

The disjoint-transposition group of order sixteen has fixed codimension three
on both the six-dimensional natural S₈ module and its seven-dimensional
augmentation cover. Actual equivariant identifications transport this fact to
the quotient and a submodule of the maximal submodule of `Ũ_H`, giving total
fixed codimension at least six.

On the other hand, if `C_A(D)` has index at most two in the critical actor,
the action on `D` is determined by one displacement map. Its image lies in
the critical commutator line, so the fixed codimension on the whole module
is at most `dim(U/D) + 1 ≤ 5`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.960, PDF p.977. The geometric
construction of the two module identifications and the index-two centralizer
remains separate. In particular, the centralizer index is not inferred here
from an abstract group-family label or from the dimensions of its modules.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
open Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- The actual six-dimensional natural S₈ module or its seven-dimensional
augmentation cover, with a specified identification of the acting group.
The augmentation core is different from the deleted permutation module. -/
def IsEightNaturalOrCover (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Equiv.Perm (Fin 8)) : Prop :=
  (∃ e : U ≃ₗ[ZMod 2] natural (Fin 8),
    ∀ g u, e (ρ g u) = naturalRepresentation (Fin 8) (eH g) (e u)) ∨
  (∃ e : U ≃ₗ[ZMod 2] core (Fin 8),
    ∀ g u, e (ρ g u) = coreRepresentation (Fin 8) (eH g) (e u))

/-- Transport of the concrete E₁₆ calculation on the two permitted models.
The same marked permutation equivalence is used for the module and actor. -/
theorem fixedCodim_eightNaturalOrCover (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Equiv.Perm (Fin 8)) (hmodel : IsEightNaturalOrCover ρ eH)
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8) :
    fixedCodim ρ A = 3 := by
  rcases hmodel with ⟨e, he⟩ | ⟨e, he⟩
  · rw [fixedCodim_map_equivariant ρ (naturalRepresentation (Fin 8))
      eH.toMonoidHom e he A, hA]
    exact Eight.fixedCodim_D.2.2.2
  · rw [fixedCodim_map_equivariant ρ (coreRepresentation (Fin 8))
      eH.toMonoidHom e he A, hA]
    exact Eight.fixedCodim_D.2.2.1

variable [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- An index-at-most-two pointwise centralizer makes one displacement map
suffice on `D`. Rank-nullity then bounds the whole fixed codimension.
Neither normality in H nor invariance of D under H is required. -/
theorem fixedCodim_le_of_critical_centralizer
    (D S : Submodule (ZMod 2) U) (A : Subgroup H)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hindex : (subspaceKernel ρ D A).relIndex A ∣ 2) :
    fixedCodim ρ A ≤ Module.finrank (ZMod 2) (U ⧸ D) +
      Module.finrank (ZMod 2) S := by
  obtain ⟨a, ha, hcoset⟩ := Subgroup.relIndex_dvd_two_iff.mp hindex
  let f : D →ₗ[ZMod 2] U := (ρ a - LinearMap.id).comp D.subtype
  have hr : LinearMap.range f ≤ S := by
    rintro _ ⟨d, rfl⟩
    exact hcomm a ha d d.property
  have hker : (LinearMap.ker f).map D.subtype ≤ fixedSpace ρ A := by
    rintro _ ⟨d, hd, rfl⟩ b
    change ρ b (d : U) = (d : U)
    have had : ρ a d = d := sub_eq_zero.mp hd
    rcases hcoset b b.property with hba | hb
    · have he := hba.2 d d.property
      simpa only [map_mul, Module.End.mul_apply, had] using he
    · exact hb.2 d d.property
  have hkdim := (Submodule.equivMapOfInjective D.subtype D.subtype_injective
    (LinearMap.ker f)).finrank_eq
  have hk := Submodule.finrank_mono hker
  have hrank := f.finrank_range_add_finrank_ker
  have hdim := D.finrank_quotient_add_finrank
  have hfixed := fixedCodim_add_finrank ρ A
  have hrdim := Submodule.finrank_mono hr
  omega

/-- The numerical contradiction, on literal submodule and quotient actions.
Its geometric application must establish the critical centralizer index. -/
theorem six_versus_five
    (W : Subrepresentation ρ) (D S : Submodule (ZMod 2) U) (A : Subgroup H)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hindex : (subspaceKernel ρ D A).relIndex A ∣ 2)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hD : Module.finrank (ZMod 2) (U ⧸ D) ≤ 4)
    (hW : 3 ≤ fixedCodim W.toRepresentation A)
    (hQ : 3 ≤ fixedCodim W.quotientRepresentation A) : False := by
  have := fixedCodim_le_of_critical_centralizer ρ D S A hcomm hindex
  have := fixedCodim_quotient_add_subrepresentation_le ρ W A
  omega

/-- The two concrete sections give fixed codimension at least six. The
submodule `J` may be `[W,H]`, so no assertion that W itself is six- or
seven-dimensional is imposed. -/
theorem six_le_fixedCodim_of_orthogonal_sections
    (W : Subrepresentation ρ) (J : Subrepresentation W.toRepresentation)
    (eH : H ≃* Equiv.Perm (Fin 8))
    (hJ : IsEightNaturalOrCover J.toRepresentation eH)
    (hQ : IsEightNaturalOrCover W.quotientRepresentation eH)
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8) :
    6 ≤ fixedCodim ρ A := by
  have hJcodim := fixedCodim_eightNaturalOrCover J.toRepresentation eH hJ A hA
  have hQcodim := fixedCodim_eightNaturalOrCover W.quotientRepresentation eH hQ A hA
  have hJle := fixedCodim_subrepresentation_le W.toRepresentation J A
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ W A
  omega

/-- The concrete orthogonal sections show that the critical actor moves D;
this is the premise used when applying F.9.13(6) in the source. -/
theorem critical_subspace_not_fixed_of_orthogonal_sections
    (W : Subrepresentation ρ) (J : Subrepresentation W.toRepresentation)
    (eH : H ≃* Equiv.Perm (Fin 8))
    (hJ : IsEightNaturalOrCover J.toRepresentation eH)
    (hQ : IsEightNaturalOrCover W.quotientRepresentation eH)
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8)
    (D : Submodule (ZMod 2) U)
    (hD : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A) :
    ¬ D ≤ fixedSpace ρ A := by
  intro hfix
  have hrank : rank A = 4 := by
    rw [← rank_map_injective eH.toMonoidHom eH.injective A, hA, Eight.rank_D]
  have hlow := six_le_fixedCodim_of_orthogonal_sections ρ W J eH hJ hQ A hA
  have := Submodule.finrank_mono hfix
  have := D.finrank_quotient_add_finrank
  have := fixedCodim_add_finrank ρ A
  omega

/-- The E₁₆ contradiction with its section dimensions discharged using the
actual natural/augmentation actions. It applies to either strong-offender
branch once its model identifications and critical centralizer are constructed. -/
theorem orthogonal_sections_contradiction
    (W : Subrepresentation ρ) (J : Subrepresentation W.toRepresentation)
    (eH : H ≃* Equiv.Perm (Fin 8))
    (hJ : IsEightNaturalOrCover J.toRepresentation eH)
    (hQ : IsEightNaturalOrCover W.quotientRepresentation eH)
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8)
    (D S : Submodule (ZMod 2) U)
    (hD : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hindex : (subspaceKernel ρ D A).relIndex A ∣ 2) : False := by
  have hrank : rank A = 4 := by
    rw [← rank_map_injective eH.toMonoidHom eH.injective A, hA, Eight.rank_D]
  have hlow := six_le_fixedCodim_of_orthogonal_sections ρ W J eH hJ hQ A hA
  have hupp := fixedCodim_le_of_critical_centralizer ρ D S A hcomm hindex
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
