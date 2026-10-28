module

public import Theory.Representation.BinaryOffender.IrreducibleDiagonal

/-!
# The diagonal in the quotient by fixed vectors

The normalizer of X acts on the literal quotient V/C_V(X). If [X,A] = X,
then A lies in that normalizer. A diagonal centralized by A cannot have an
X-invariant image in this quotient: the commutator identity would make that
image X-fixed, and disjointness of the two irreducible images would force
[I,X] into C_V(X), contradicting I = [I,X].

This argument is entirely in the quotient. It does not lift invariance modulo
C_V(X) to invariance of a subspace of V.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.7.2(1), printed p. 119 (PDF p. 130).
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Normalizers preserve the space of fixed vectors. -/
theorem normalizer_le_fixedSpace_stabilizer (X : Subgroup G) :
    (Subgroup.normalizer (X : Set G)) ≤ subspaceStabilizer ρ (fixedSpace ρ X) := by
  apply le_subspaceStabilizer
  intro g hg v hv x
  have hy : g⁻¹ * (x : G) * g ∈ X :=
    by simpa only [inv_inv] using
      ((Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hg)) x).mp x.property
  have he := hv ⟨g⁻¹ * (x : G) * g, hy⟩
  have he' := congrArg (fun w => ρ g w) he
  change ρ g (ρ (g⁻¹ * (x : G) * g) v) = ρ g v at he'
  change ρ (x : G) (ρ g v) = ρ g v
  simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left] using he'

/-- Fixed vectors, as a subrepresentation of the normalizer action. -/
noncomputable def normalizerFixedSubrepresentation (X : Subgroup G) :
    Subrepresentation (ρ.comp (Subgroup.normalizer (X : Set G)).subtype) :=
  ⟨fixedSpace ρ X, fun g _ hv => (normalizer_le_fixedSpace_stabilizer ρ X g.property _).2 hv⟩

/-- The induced normalizer action on the actual quotient V/C_V(X). -/
noncomputable def normalizerQuotientRepresentation (X : Subgroup G) :
    Representation (ZMod 2) (Subgroup.normalizer (X : Set G)) (V ⧸ fixedSpace ρ X) :=
  (normalizerFixedSubrepresentation ρ X).quotientRepresentation

@[simp] theorem normalizerQuotientRepresentation_mk (X : Subgroup G)
    (g : (Subgroup.normalizer (X : Set G))) (v : V) :
    normalizerQuotientRepresentation ρ X g ((fixedSpace ρ X).mkQ v) =
      (fixedSpace ρ X).mkQ (ρ g v) := rfl

private theorem commutator_subgroupOf_eq_self {X A N : Subgroup G}
    (hX : X ≤ N) (hA : A ≤ N) (hXA : ⁅X, A⁆ = X) :
    ⁅X.subgroupOf N, A.subgroupOf N⁆ = X.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
    Subgroup.map_subgroupOf_eq_of_le hA, hXA]

/-- The image of the a-diagonal cannot be X-invariant, even modulo C_V(X). -/
theorem IsIrrPlus.quotient_diagonal_not_invariant
    {X A : Subgroup G} {I : Submodule (ZMod 2) V} {a : G}
    (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (hXA : ⁅X, A⁆ = X)
    (ha : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v) :
    ¬ X.subgroupOf (Subgroup.normalizer (X : Set G)) ≤
      subspaceStabilizer (normalizerQuotientRepresentation ρ X)
        ((diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ) := by
  intro hstab
  let σ := normalizerQuotientRepresentation ρ X
  let D := (diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ
  have hAN : A ≤ (Subgroup.normalizer (X : Set G)) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hXA.le
  have hfixA : D ≤ fixedSpace σ (A.subgroupOf (Subgroup.normalizer (X : Set G))) := by
    rintro _ ⟨d, ⟨i, hi, rfl⟩, rfl⟩ b
    change (fixedSpace ρ X).mkQ (ρ b.val (ρ a i - i)) = _
    rw [ha b.val b.property i]
    rfl
  have hfixX : D ≤ fixedSpace σ (X.subgroupOf (Subgroup.normalizer (X : Set G))) := by
    rw [← commutator_subgroupOf_eq_self X.le_normalizer hAN hXA]
    exact le_fixedSpace_commutator_of_invariant σ hstab hfixA
  have hcomm : subspaceCommutator ρ I X ≤ fixedSpace ρ X := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, i, hi, rfl⟩
    have hd : (fixedSpace ρ X).mkQ (ρ a i - i) ∈ D :=
      ⟨ρ a i - i, ⟨i, hi, rfl⟩, rfl⟩
    have hxd := hfixX hd ⟨⟨x, X.le_normalizer hx⟩, hx⟩
    change (fixedSpace ρ X).mkQ (ρ x (ρ a i - i)) =
      (fixedSpace ρ X).mkQ (ρ a i - i) at hxd
    rw [map_sub, map_sub, map_sub] at hxd
    have he : (fixedSpace ρ X).mkQ (ρ x (ρ a i) - ρ a i) =
        (fixedSpace ρ X).mkQ (ρ x i - i) := by
      rw [map_sub, map_sub]
      exact (sub_eq_sub_iff_sub_eq_sub).mp hxd
    have hdis := IsIrrPlus.disjoint_quotientImages ρ hI hIa hne
    have hm : (fixedSpace ρ X).mkQ (ρ x i - i) ∈
        I.map (fixedSpace ρ X).mkQ ⊓ (I.map (ρ a)).map (fixedSpace ρ X).mkQ := by
      refine ⟨⟨_, I.sub_mem ((hI.choose hx i).2 hi) hi, rfl⟩, ?_⟩
      have hai : ρ a i ∈ I.map (ρ a) := ⟨i, hi, rfl⟩
      exact ⟨_, (I.map (ρ a)).sub_mem ((hIa.choose hx _).2 hai) hai, he⟩
    rw [hdis.eq_bot] at hm
    exact (Submodule.Quotient.mk_eq_zero _).mp hm
  rw [hI.choose_spec.1] at hcomm
  exact hI.not_le_fixedSpace ρ hcomm
end Representation.BinaryOffender
