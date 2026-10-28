module

public import Theory.Representation.NonsplitFour
public import Theory.Representation.EndFieldRep
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Singer centralizers and normalizer action in dimension four

A nontrivial subgroup of `GL(4,q)` of order dividing `q² + 1`, for even `q`,
acts irreducibly. Schur's lemma and the finite division ring theorem make its
commuting algebra a field. Evaluation at a nonzero vector bounds the degree
of this field by four. Its units are cyclic, giving the centralizer assertion.
For a cyclic subgroup, normalizer conjugation acts on this field by a power
of the `q`-Frobenius, simultaneously on all subgroup elements.

The conjugation convention is **right conjugation**, `u ↦ g⁻¹ * u * g`.
Source: Huppert--Blackburn, *Finite Groups III*, XI.3.10(a), printed
pp. 190–191, citing II.7.3.
-/

noncomputable section

namespace Representation

open scoped MonoidAlgebra IsMulCommutative

section CommutingAlgebra

variable {K A V : Type*} [Field K] [Monoid A] [AddCommGroup V] [Module K V]
    (ρ : Representation K A V)

private abbrev commutingAlgebra := Subalgebra.centralizer K (Set.range ρ)

private def commutingIntertwiner (f : commutingAlgebra ρ) : IntertwiningMap ρ ρ where
  toLinearMap := f.val
  isIntertwining' a := (f.property (ρ a) ⟨a, rfl⟩).symm

private def commutingToEnd : commutingAlgebra ρ →ₐ[K] Module.End K[A] ρ.asModule :=
  (IntertwiningMap.equivAlgEnd (ρ := ρ)).toAlgHom.comp
    { toFun := commutingIntertwiner ρ
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

private theorem commutingToEnd_injective : Function.Injective (commutingToEnd ρ) := by
  intro f g h
  apply Subtype.ext
  exact congrArg IntertwiningMap.toLinearMap
    ((IntertwiningMap.equivAlgEnd (ρ := ρ)).injective h)

variable [Finite K] [FiniteDimensional K V]

private instance commuting_finite : Finite (commutingAlgebra ρ) :=
  Finite.of_injective (commutingToEnd ρ) (commutingToEnd_injective ρ)

variable [IsIrreducible ρ]

@[instance_reducible]
private noncomputable def commutingField : Field (commutingAlgebra ρ) := by
  let : IsDomain (commutingAlgebra ρ) :=
    Function.Injective.isDomain (commutingToEnd ρ) (commutingToEnd_injective ρ)
  exact (Finite.isDomain_to_isField (commutingAlgebra ρ)).toField

omit [Finite K] [FiniteDimensional K V] in
private theorem commuting_eval_injective (v : V) (hv : v ≠ 0) :
    Function.Injective (fun f : commutingAlgebra ρ => f.val v) := by
  intro f g h
  have hz : (commutingIntertwiner ρ (f - g)) v = 0 := sub_eq_zero.mpr h
  rcases IsIrreducible.injective_or_eq_zero (commutingIntertwiner ρ (f - g)) with hi | he
  · have hzero : (commutingIntertwiner ρ (f - g)) 0 = 0 := map_zero _
    exact (hv (hi (hz.trans hzero.symm))).elim
  · apply sub_eq_zero.mp
    apply Subtype.ext
    exact congrArg IntertwiningMap.toLinearMap he

omit [Finite K] in
private theorem commuting_finrank_le :
    Module.finrank K (commutingAlgebra ρ) ≤ Module.finrank K V := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let ev : commutingAlgebra ρ →ₗ[K] V :=
    { toFun := fun f => f.val v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearMap.finrank_le_finrank_of_injective (f := ev)
    (commuting_eval_injective ρ v hv)

end CommutingAlgebra

section Four

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

private abbrev matrixAction : GL (Fin 4) K →* Module.End K (Fin 4 → K) :=
  (Units.coeHom _).comp Matrix.GeneralLinearGroup.toLin.toMonoidHom

private abbrev subgroupAction (C : Subgroup (GL (Fin 4) K)) :
    Representation K C (Fin 4 → K) := matrixAction.comp C.subtype

omit [Fintype K] [CharP K 2] in
private theorem matrixAction_injective : Function.Injective (matrixAction (K := K)) := by
  intro a b h
  apply Matrix.GeneralLinearGroup.toLin.injective
  exact Units.ext h

private theorem subgroupAction_irreducible (C : Subgroup (GL (Fin 4) K))
    (hC : C ≠ ⊥) (hcard : Nat.card C ∣ Fintype.card K ^ 2 + 1) :
    IsIrreducible (subgroupAction C) := by
  let : Nontrivial C := ((Subgroup.nontrivial_iff_ne_bot C).mpr hC)
  refine ⟨fun U => ?_⟩
  have h := invariant_eq_bot_or_top_of_card_dvd_sq_add_one
    (subgroupAction C) (matrixAction_injective.comp C.subtype_injective)
    (by simp) hcard (by exact Fintype.one_lt_card)
    (Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq K 2)))
    U.toSubmodule (fun a v hv => U.apply_mem_toSubmodule a hv)
  rcases h with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

private def centralizerToAlgebra (C : Subgroup (GL (Fin 4) K)) :
    Subgroup.centralizer (C : Set (GL (Fin 4) K)) →* commutingAlgebra (subgroupAction C) where
  toFun g := ⟨matrixAction g.val, by
    rintro _ ⟨u, rfl⟩
    simpa only [map_mul, subgroupAction, MonoidHom.comp_apply, Subgroup.subtype_apply] using
      congrArg matrixAction (Subgroup.mem_centralizer_iff.mp g.property u.val u.property)⟩
  map_one' := Subtype.ext (map_one matrixAction)
  map_mul' g h := Subtype.ext (map_mul matrixAction g.val h.val)

/-- The ambient centralizer of a nontrivial subgroup of order dividing `q²+1`
in `GL(4,q)`, for `q` even, is cyclic. No cyclicity assumption on the subgroup
is needed. -/
public theorem isCyclic_centralizer_of_card_dvd_sq_add_one
    (C : Subgroup (GL (Fin 4) K)) (hC : C ≠ ⊥)
    (hcard : Nat.card C ∣ Fintype.card K ^ 2 + 1) :
    IsCyclic (Subgroup.centralizer (C : Set (GL (Fin 4) K))) := by
  let := subgroupAction_irreducible C hC hcard
  let := commutingField (subgroupAction C)
  let f := (centralizerToAlgebra C).toHomUnits
  apply isCyclic_of_injective f
  intro a b h
  apply Subtype.ext
  apply matrixAction_injective
  exact congrArg (fun u => (u.val : commutingAlgebra (subgroupAction C)).val) h

private def matrixRightConj (g : GL (Fin 4) K) :
    Module.End K (Fin 4 → K) ≃ₐ[K] Module.End K (Fin 4 → K) :=
  (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.symm.conjAlgEquiv K

omit [Fintype K] [CharP K 2] in
private theorem matrixRightConj_action (g u : GL (Fin 4) K) :
    matrixRightConj g (matrixAction u) = matrixAction (g⁻¹ * u * g) := by
  simp only [map_mul]
  change _ = (↑(Matrix.GeneralLinearGroup.toLin (g⁻¹)) : Module.End K (Fin 4 → K)) *
    ↑(Matrix.GeneralLinearGroup.toLin u) * ↑(Matrix.GeneralLinearGroup.toLin g)
  rw [map_inv]
  rfl

omit [Fintype K] [CharP K 2] in
private theorem matrixRightConj_mem (C : Subgroup (GL (Fin 4) K))
    (g : GL (Fin 4) K) (hg : g ∈ Subgroup.normalizer (C : Set (GL (Fin 4) K)))
    (f : commutingAlgebra (subgroupAction C)) :
    matrixRightConj g f.val ∈ commutingAlgebra (subgroupAction C) := by
  rintro _ ⟨u, rfl⟩
  have hu : g * u.val * g⁻¹ ∈ C :=
    (Subgroup.mem_normalizer_iff.mp hg u.val).mp u.property
  have hf := f.property _ ⟨⟨g * u.val * g⁻¹, hu⟩, rfl⟩
  have he := congrArg (matrixRightConj g) hf
  simp only [map_mul] at he
  change matrixRightConj g (matrixAction (g * u.val * g⁻¹)) * _ =
    _ * matrixRightConj g (matrixAction (g * u.val * g⁻¹)) at he
  rw [matrixRightConj_action] at he
  have hcancel : g⁻¹ * (g * u.val * g⁻¹) * g = u.val := by group
  rw [hcancel] at he
  exact he

private def normalizerAlgebraAut (C : Subgroup (GL (Fin 4) K))
    (g : GL (Fin 4) K) (hg : g ∈ Subgroup.normalizer (C : Set (GL (Fin 4) K))) :
    commutingAlgebra (subgroupAction C) ≃ₐ[K] commutingAlgebra (subgroupAction C) := by
  let f : commutingAlgebra (subgroupAction C) →ₐ[K]
      commutingAlgebra (subgroupAction C) :=
    ((matrixRightConj g).toAlgHom.comp (commutingAlgebra (subgroupAction C)).val).codRestrict
      _ (matrixRightConj_mem C g hg)
  apply AlgEquiv.ofBijective f
  apply (Finite.injective_iff_bijective).mp
  intro a b hab
  apply Subtype.ext
  exact (matrixRightConj g).injective (congrArg Subtype.val hab)

/-- Every normalizer element acts on the whole cyclic subgroup by one common
power of Frobenius. Conjugation is on the right: `g⁻¹ * u * g`. -/
public theorem normalizer_eq_frobenius_pow_of_card_dvd_sq_add_one
    (C : Subgroup (GL (Fin 4) K)) (hC : C ≠ ⊥) [IsCyclic C]
    (hcard : Nat.card C ∣ Fintype.card K ^ 2 + 1)
    (g : GL (Fin 4) K) (hg : g ∈ Subgroup.normalizer (C : Set (GL (Fin 4) K))) :
    ∃ i : ℕ, i < 4 ∧ ∀ u ∈ C, g⁻¹ * u * g = u ^ (Fintype.card K ^ i) := by
  let := subgroupAction_irreducible C hC hcard
  let := commutingField (subgroupAction C)
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    K (commutingAlgebra (subgroupAction C))).surjective (normalizerAlgebraAut C g hg)
  refine ⟨i.val, lt_of_lt_of_le i.isLt ?_, ?_⟩
  · simpa using commuting_finrank_le (subgroupAction C)
  · intro u hu
    have humem : matrixAction u ∈ commutingAlgebra (subgroupAction C) := by
      rintro _ ⟨v, rfl⟩
      have hcomm : v.val * u = u * v.val :=
        congrArg Subtype.val (mul_comm v (⟨u, hu⟩ : C))
      simpa only [map_mul, subgroupAction, MonoidHom.comp_apply, Subgroup.subtype_apply] using
        congrArg matrixAction hcomm
    let uf : commutingAlgebra (subgroupAction C) := ⟨matrixAction u, humem⟩
    have hpow := DFunLike.congr_fun hi uf
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at hpow
    apply matrixAction_injective
    have hval := congrArg Subtype.val hpow.symm
    change matrixRightConj g (matrixAction u) = (uf ^ (Fintype.card K ^ i.val)).val at hval
    rw [matrixRightConj_action] at hval
    simpa only [Subalgebra.coe_pow, uf, map_pow] using hval

end Four

end Representation
