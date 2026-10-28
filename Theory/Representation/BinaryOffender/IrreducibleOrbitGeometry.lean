module

public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction

/-!
# Geometry of regular irreducible-section orbits

Normalizer transport preserves invariant subspaces and their dimensions.
Irreducibility separates the original member from any distinct invariant
translate of the same dimension; transporting this separation gives pairwise
disjoint quotient images throughout a regular orbit. This avoids changing
or assuming an irreducibility instance for each translate.

In V/C_V(X), two complementary translates have total dimension 2n, while
their diagonal has dimension n. Factoring the displacement map through
V/C_V(A) bounds n by the fixed-space codimension of A.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.7.2(1), printed p. 119 (PDF p. 130).
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- An invertible representation operator preserves subspace dimension. -/
theorem finrank_map_action (I : Submodule (ZMod 2) V) (g : G) :
    Module.finrank (ZMod 2) (I.map (ρ g)) = Module.finrank (ZMod 2) I := by
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
    (ρ.asGroupHom g)).finrank_map_eq I

/-- Every group element acts by an injective linear map. -/
theorem action_injective (g : G) : Function.Injective (ρ g) := by
  intro v w h
  have := congrArg (ρ g⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using this

/-- Equal-dimensional invariant spaces can be separated from an irreducible
section without transporting the irreducibility instance. -/
theorem IsIrrPlus.disjoint_quotientImage_of_finrank_eq [FiniteDimensional (ZMod 2) V]
    {X : Subgroup G} {I J : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) (hJ : X ≤ subspaceStabilizer ρ J)
    (hdim : Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) J) (hne : I ≠ J) :
    Disjoint (I.map (fixedSpace ρ X).mkQ) (J.map (fixedSpace ρ X).mkQ) := by
  have hle : I ⊓ (J ⊔ fixedSpace ρ X) ≤ fixedSpace ρ X :=
    (IsIrrPlus.le_or_inf_sup_fixedSpace_le ρ hI hJ).resolve_left
      (fun h => hne (Submodule.eq_of_le_of_finrank_eq h hdim))
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro q hq
  obtain ⟨i, hi, rfl⟩ := hq.1
  obtain ⟨j, hj, heq⟩ := hq.2
  have hdiff : i - j ∈ fixedSpace ρ X := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (fixedSpace ρ X).mkQ (i - j) = 0
    rw [map_sub, heq, sub_self]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply hle
  refine ⟨hi, Submodule.mem_sup.mpr ⟨j, hj, i - j, hdiff, ?_⟩⟩
  abel

/-- A regular normalizer orbit has pairwise disjoint images modulo the fixed space. -/
theorem quotientOrbit_pairwise_disjoint [FiniteDimensional (ZMod 2) V]
    {X A : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hstab : A ⊓ subspaceStabilizer ρ I = ⊥) :
    Pairwise (fun b c : A => Disjoint
      ((I.map (ρ b)).map (fixedSpace ρ X).mkQ)
      ((I.map (ρ c)).map (fixedSpace ρ X).mkQ)) := by
  intro b c hbc
  let g : G := (b : G)⁻¹ * c
  have hgA : g ∈ A := A.mul_mem (A.inv_mem b.property) c.property
  have hg : g ∈ Subgroup.normalizer (X : Set G) := hAN hgA
  have hne : I ≠ I.map (ρ g) := by
    intro he
    have he' := congrArg (fun J : Submodule (ZMod 2) V => J.map (ρ b)) he
    rw [← subspace_map_mul] at he'
    have hbg : (b : G) * g = c := mul_inv_cancel_left _ _
    rw [hbg] at he'
    exact hbc (subspace_orbitMap_injective ρ hstab he')
  have hdis := hI.disjoint_quotientImage_of_finrank_eq ρ
    (map_subspace_invariant_of_mem_normalizer ρ hI.choose hg)
    (finrank_map_action ρ I g).symm hne
  have hmap := Submodule.disjoint_map
    (action_injective (normalizerQuotientRepresentation ρ X) ⟨b, hAN b.property⟩) hdis
  rw [← quotientImage_map_normalizer, ← quotientImage_map_normalizer,
    ← subspace_map_mul] at hmap
  have hbg : (b : G) * g = c := mul_inv_cancel_left _ _
  simpa only [hbg] using hmap

/-- All normalizer translates have the same dimension in the fixed-space quotient. -/
theorem finrank_quotientOrbit (X : Subgroup G) (I : Submodule (ZMod 2) V)
    {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    Module.finrank (ZMod 2) ((I.map (ρ g)).map (fixedSpace ρ X).mkQ) =
      Module.finrank (ZMod 2) (I.map (fixedSpace ρ X).mkQ) := by
  rw [quotientImage_map_normalizer ρ X I ⟨g, hg⟩]
  exact finrank_map_action _ _ _

/-- A member of Irr⁺ has a nonzero image modulo fixed vectors. -/
theorem IsIrrPlus.finrank_quotientImage_pos [FiniteDimensional (ZMod 2) V]
    {X : Subgroup G} {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) :
    0 < Module.finrank (ZMod 2) (I.map (fixedSpace ρ X).mkQ) := by
  by_contra hn
  have he := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos hn)
  apply hI.not_le_fixedSpace ρ
  intro i hi
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have hm : (fixedSpace ρ X).mkQ i ∈ I.map (fixedSpace ρ X).mkQ := ⟨i, hi, rfl⟩
  rwa [he] at hm
end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The diagonal of two disjoint translates has the dimension of either summand. -/
theorem finrank_diagonal_eq_of_disjoint (I : Submodule (ZMod 2) V) (a : G)
    (hdis : Disjoint I (I.map (ρ a))) :
    Module.finrank (ZMod 2) (diagonalSubspace ρ I a) = Module.finrank (ZMod 2) I := by
  have hinj : Function.Injective ((ρ a - LinearMap.id).domRestrict I) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro v hv
    change v = 0
    apply Subtype.ext
    have hf : ρ a (v : V) = v := sub_eq_zero.mp hv
    have hm : (v : V) ∈ I ⊓ I.map (ρ a) := ⟨v.property, ⟨v, v.property, hf⟩⟩
    rwa [hdis.eq_bot] at hm
  rw [diagonalSubspace, ← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj hinj

/-- Taking the diagonal commutes with the actual quotient action. -/
theorem quotient_diagonal_eq (X : Subgroup G) (I : Submodule (ZMod 2) V)
    (g : Subgroup.normalizer (X : Set G)) :
    (diagonalSubspace ρ I g).map (fixedSpace ρ X).mkQ =
      diagonalSubspace (normalizerQuotientRepresentation ρ X)
        (I.map (fixedSpace ρ X).mkQ) g := by
  unfold diagonalSubspace
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

/-- Two complementary translates give a quotient of twice their common dimension. -/
theorem finrank_quotient_eq_double [FiniteDimensional (ZMod 2) V]
    {X : Subgroup G} {I : Submodule (ZMod 2) V} {a : G}
    (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (haN : a ∈ Subgroup.normalizer (X : Set G))
    (hsup : I ⊔ I.map (ρ a) = ⊤) :
    Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ X) =
      2 * Module.finrank (ZMod 2) (I.map (fixedSpace ρ X).mkQ) := by
  have hd := (I.map (fixedSpace ρ X).mkQ).finrank_sup_add_finrank_inf_eq
    ((I.map (ρ a)).map (fixedSpace ρ X).mkQ)
  have hsupq : I.map (fixedSpace ρ X).mkQ ⊔ (I.map (ρ a)).map (fixedSpace ρ X).mkQ = ⊤ := by
    rw [← Submodule.map_sup, hsup, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)
  rw [(IsIrrPlus.disjoint_quotientImages ρ hI hIa hne).eq_bot, hsupq,
    finrank_quotientOrbit ρ X I haN] at hd
  simpa only [Module.finrank_self, finrank_top, finrank_bot, add_zero, two_mul] using hd

/-- The quotient diagonal has the common dimension of the two irreducible images. -/
theorem finrank_quotientDiagonal_eq [FiniteDimensional (ZMod 2) V]
    {X : Subgroup G} {I : Submodule (ZMod 2) V} {a : G}
    (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (haN : a ∈ Subgroup.normalizer (X : Set G)) :
    Module.finrank (ZMod 2) ((diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ) =
      Module.finrank (ZMod 2) (I.map (fixedSpace ρ X).mkQ) := by
  rw [quotient_diagonal_eq ρ X I ⟨a, haN⟩]
  apply finrank_diagonal_eq_of_disjoint
  rw [← quotientImage_map_normalizer]
  exact IsIrrPlus.disjoint_quotientImages ρ hI hIa hne

/-- The diagonal image factors through V/C_V(A), giving the codimension bound. -/
theorem finrank_quotientDiagonal_le_fixedCodim [FiniteDimensional (ZMod 2) V]
    (X A : Subgroup G) (I : Submodule (ZMod 2) V) {a : G} (ha : a ∈ A) :
    Module.finrank (ZMod 2) ((diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ) ≤
      fixedCodim ρ A := by
  let f := (fixedSpace ρ X).mkQ.comp (ρ a - LinearMap.id)
  have hle : fixedSpace ρ A ≤ f.ker := by
    intro v hv
    change (fixedSpace ρ X).mkQ (ρ a v - v) = 0
    have hf : ρ a v = v := hv ⟨a, ha⟩
    rw [hf, sub_self, map_zero]
  have him : (diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ ≤ f.range := by
    rintro _ ⟨d, ⟨i, _hi, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  have hdim := Submodule.finrank_mono hle
  have himdim := Submodule.finrank_mono him
  have hr := f.finrank_range_add_finrank_ker
  have hc := fixedCodim_add_finrank ρ A
  omega
end Representation.BinaryOffender
