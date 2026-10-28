module

public import BenderSuzuki.Converse.PSL2
public import Theory.SpecificGroups.SL2.OddAbelianSubgroups
public import Theory.GroupTheory.OddInvertedSubgroups

/-!
# Cyclic subgroups in the linear branch of Proposition 16.5

In characteristic two the literal projection SL₂ → PSL₂ is injective.
Thus an odd p-subgroup of a linear model is cyclic by its faithful SL₂
representation. An odd subgroup inverted by an element of a normalized
linear subgroup first lies in that subgroup and is abelian, hence cyclic.

The last theorem states the relative normalization and inverter containment
needed when the model is a normal subgroup of a larger centralizer. An
unrelated model isomorphism would not suffice.
Source: GLS, Volume 4, Chapter 2, Proposition 16.5, and Chapter 4, Lemma 3.7.
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G]
variable {k : Type*} [Field k] [CharP k 2]

private noncomputable def linearLift (F : Subgroup G) (e : F ≃* PSL2MatrixGroup k)
    (R : Subgroup G) (hRF : R ≤ F) : R →* Matrix.SpecialLinearGroup (Fin 2) k :=
  (MulEquiv.ofBijective (Converse.pi k)
    ⟨Converse.pi_injective, Converse.pi_surjective⟩).symm.toMonoidHom.comp
      (e.toMonoidHom.comp (inclusion hRF))

private theorem linearLift_injective (F : Subgroup G) (e : F ≃* PSL2MatrixGroup k)
    (R : Subgroup G) (hRF : R ≤ F) : Function.Injective (linearLift F e R hRF) :=
  (MulEquiv.ofBijective (Converse.pi k)
    ⟨Converse.pi_injective, Converse.pi_surjective⟩).symm.injective.comp
      (e.injective.comp (inclusion_injective hRF))

variable [Finite G]

/-- The odd p-subgroups `R_u`, `R_v` in the source are cyclic as soon as
their containment in the actual linear component has been established. -/
public theorem pSubgroup_isCyclic_of_linear_model (F : Subgroup G)
    (e : F ≃* PSL2MatrixGroup k) (R : Subgroup G) (hRF : R ≤ F)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hR : IsPGroup p R) : IsCyclic R :=
  Matrix.SL2.odd_pGroup_isCyclic_of_injective hR hp
    (linearLift F e R hRF) (linearLift_injective F e R hRF)

/-- An odd subgroup inverted by an element of a normalized linear model
is contained in that model and cyclic. Only relative normalization is used. -/
public theorem odd_inverted_subgroup_le_and_isCyclic (F : Subgroup G)
    (e : F ≃* PSL2MatrixGroup k) (R : Subgroup G)
    (hodd : Odd (Nat.card R)) (hnorm : R ≤ normalizer F)
    (t : G) (ht : t ∈ F) (hinv : ∀ x ∈ R, t * x * t⁻¹ = x⁻¹) :
    R ≤ F ∧ IsCyclic R := by
  have hRF := le_of_odd_inverted_of_le_normalizer R F hodd hnorm t ht hinv
  let : IsMulCommutative R := isMulCommutative_of_inverted R t hinv
  exact ⟨hRF, Matrix.SL2.odd_abelian_isCyclic_of_injective hodd
    (linearLift F e R hRF) (linearLift_injective F e R hRF)⟩

end BenderSuzuki.ZD.RankOneModelGeometry
