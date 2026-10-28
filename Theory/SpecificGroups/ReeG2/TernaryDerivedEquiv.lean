module

public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv.MatrixCoordinates
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.ReeG2.Order
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The derived subgroup of the ternary Ree group from a concrete embedding

Any nontrivial homomorphism from PSL₂(8) into the literal Ree matrix model
is injective, by simplicity. Its perfect image has index three. Conjugate
perfect subgroups act trivially on the three cosets, so the image is normal;
the cyclic quotient then identifies it with the entire commutator subgroup.

The two remaining construction inputs are separated through the explicit
nine-point permutation group in `Generators`: a projective identification
and a nontrivial matrix homomorphism. Neither is assumed to exist here.
The resulting equivalence is conditional until both are constructed.

Source: GLS III §2.2, A₁(8) ≅ ²G₂(3)′, and Theorem 2.5.15;
Aschbacher–Smith B.1.13, printed pp.73–74.
-/

public section

open Subgroup
open scoped MatrixGroups

namespace Atlas.ReeG2.TernaryDerived

private theorem psl_card : Nat.card PSL(2, GaloisField 2 3) = 504 := by
  have hF : Nat.card (GaloisField 2 3) = 8 := by
    simpa using GaloisField.card 2 3 (by decide)
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := GaloisField 2 3) 2
  norm_num [hF, Fin.prod_univ_succ] at h
  omega

private theorem psl_perfect : Group.IsPerfect PSL(2, GaloisField 2 3) := by
  have hF : Nat.card (GaloisField 2 3) = 8 := by
    simpa using GaloisField.card 2 3 (by decide)
  obtain ⟨u, hu⟩ := exists_pow_ne_one_of_isCyclic
    (G := (GaloisField 2 3)ˣ) (by decide : 2 ≠ 0)
    (by rw [Nat.card_units, hF]; decide : 2 < Nat.card (GaloisField 2 3)ˣ)
  refine ⟨SL2Simple.PSL_commutator_eq_top ⟨u, Units.ne_zero u, ?_⟩⟩
  intro h
  exact hu (Units.ext (by simpa using h))

private theorem perfect_index_three {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Group.IsPerfect H] (hi : H.index = 3) :
    H = commutator G := by
  have hn : H.Normal := by
    constructor
    intro x hx g
    let f := (MulAut.conj g).toMonoidHom
    let : Group.IsPerfect (H.map f) := Group.IsPerfect.map f
    exact le_of_isPerfect_of_index_le_four (H.map f) H (by omega) ⟨x, hx, rfl⟩
  let := hn
  let : IsCyclic (G ⧸ H) := isCyclic_of_prime_card (by exact hi : Nat.card (G ⧸ H) = 3)
  let : CommGroup (G ⧸ H) := IsCyclic.commGroup
  apply le_antisymm
  · rw [← H.commutator_eq_self]
    exact Subgroup.commutator_mono le_top le_top
  · simpa only [QuotientGroup.ker_mk'] using
      Abelianization.commutator_subset_ker (QuotientGroup.mk' H)

private theorem psl_hom_injective
    (f : PSL(2, GaloisField 2 3) →* Model (ZMod 3) 0) (hf : f ≠ 1) :
    Function.Injective f := by
  let : IsSimpleGroup PSL(2, GaloisField 2 3) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      have hc := GaloisField.card 2 3 (by decide)
      norm_num at hc
      omega)
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff f).mp h
  · exact (hf (MonoidHom.ker_eq_top_iff.mp h)).elim

private theorem psl_hom_range
    (f : PSL(2, GaloisField 2 3) →* Model (ZMod 3) 0) (hf : f ≠ 1) :
    f.range = commutator (Model (ZMod 3) 0) := by
  let : Group.IsPerfect PSL(2, GaloisField 2 3) := psl_perfect
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hR : Nat.card (Model (ZMod 3) 0) = 1512 := by
    have h := Atlas.ReeG2.order (F := ZMod 3) 0 (by norm_num)
    norm_num at h
    exact h
  have hH : Nat.card f.range = 504 :=
    (Nat.card_congr (MonoidHom.ofInjective (psl_hom_injective f hf)).toEquiv).symm.trans psl_card
  apply perfect_index_three
  have hi := f.range.card_mul_index
  rw [hH, hR] at hi
  omega

/-- A concrete nontrivial homomorphism determines the exceptional isomorphism.
Its inverse is the original homomorphism, with codomain restricted to the derived group. -/
noncomputable def equivOfNontrivialHom
    (f : PSL(2, GaloisField 2 3) →* Model (ZMod 3) 0) (hf : f ≠ 1) :
    commutator (Model (ZMod 3) 0) ≃* PSL(2, GaloisField 2 3) :=
  (MulEquiv.subgroupCongr (psl_hom_range f hf).symm).trans
    (MonoidHom.ofInjective (psl_hom_injective f hf)).symm

@[simp] theorem equivOfNontrivialHom_symm_apply
    (f : PSL(2, GaloisField 2 3) →* Model (ZMod 3) 0) (hf : f ≠ 1)
    (x : PSL(2, GaloisField 2 3)) :
    ((equivOfNontrivialHom f hf).symm x).val = f x := by
  exact MonoidHom.ofInjective_apply (psl_hom_injective f hf)

private theorem comparison_hom_ne_one
    (e : PermutationModel ≃* PSL(2, GaloisField 2 3))
    (f : PermutationModel →* Model (ZMod 3) 0) (hf : f ≠ 1) :
    f.comp e.symm.toMonoidHom ≠ 1 := by
  intro h
  apply hf
  apply MonoidHom.ext
  intro x
  have hx := congrArg (fun k : PSL(2, GaloisField 2 3) →* Model (ZMod 3) 0 => k (e x)) h
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, MonoidHom.one_apply] using hx

/-- Assembly of the independently constructed projective and matrix maps.
The inputs assert no equality with the Ree commutator subgroup. -/
noncomputable def equivOfPermutationModel
    (e : PermutationModel ≃* PSL(2, GaloisField 2 3))
    (f : PermutationModel →* Model (ZMod 3) 0) (hf : f ≠ 1) :
    commutator (Model (ZMod 3) 0) ≃* PSL(2, GaloisField 2 3) :=
  equivOfNontrivialHom (f.comp e.symm.toMonoidHom) (comparison_hom_ne_one e f hf)

@[simp] theorem equivOfPermutationModel_symm_apply
    (e : PermutationModel ≃* PSL(2, GaloisField 2 3))
    (f : PermutationModel →* Model (ZMod 3) 0) (hf : f ≠ 1)
    (x : PSL(2, GaloisField 2 3)) :
    ((equivOfPermutationModel e f hf).symm x).val = f (e.symm x) := by
  exact equivOfNontrivialHom_symm_apply (f.comp e.symm.toMonoidHom)
    (comparison_hom_ne_one e f hf) x

end Atlas.ReeG2.TernaryDerived
