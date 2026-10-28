module

public import Theory.Representation.BinaryOffender.IrreducibleQuotientDiagonal
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Regular subspace orbits and invariant complements

A trivial intersection with the subspace stabilizer makes the orbit map
injective, so its range has the order of the acting subgroup. Normalizers
transport invariant subspaces, and this transport commutes with taking the
literal quotient by fixed vectors.

We also prove that a fixed subspace disjoint from one orbit member is disjoint
from the whole orbit, and that a complement in a partition by invariant
subspaces is invariant. These are the action-theoretic steps of the regular
orbit argument in B.7.2(1); the finite-geometry counting is separate.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.7.2, printed p. 119 (PDF p. 130).
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The representation acts on subspaces by taking images. -/
theorem subspace_map_mul (I : Submodule (ZMod 2) V) (g h : G) :
    I.map (ρ (g * h)) = (I.map (ρ h)).map (ρ g) := by
  rw [map_mul]
  exact Submodule.map_comp (ρ h) (ρ g) I

/-- A subspace has unchanged image precisely under its stabilizer. -/
theorem subspace_map_eq_iff (I : Submodule (ZMod 2) V) (g : G) :
    I.map (ρ g) = I ↔ g ∈ subspaceStabilizer ρ I := by
  have hinv (v : V) : ρ g⁻¹ (ρ g v) = v := by
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  constructor
  · intro h v
    constructor
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, he⟩ := hv
      have : w = v := by simpa only [hinv] using congrArg (ρ g⁻¹) he
      exact this ▸ hw
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩
  · intro h
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (h v).2 hv
    · intro v hv
      refine ⟨ρ g⁻¹ v, ?_, ?_⟩
      · exact ((subspaceStabilizer ρ I).inv_mem h v).2 hv
      · simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply]

/-- A trivial stabilizer makes the orbit map injective. -/
theorem subspace_orbitMap_injective {A : Subgroup G} {I : Submodule (ZMod 2) V}
    (hstab : A ⊓ subspaceStabilizer ρ I = ⊥) :
    Function.Injective (fun b : A => I.map (ρ b)) := by
  intro b c h
  change I.map (ρ b) = I.map (ρ c) at h
  have he : I.map (ρ ((c : G)⁻¹ * b)) = I := by
    rw [subspace_map_mul, h, ← subspace_map_mul, inv_mul_cancel, map_one]
    exact Submodule.map_id I
  have hm : (c : G)⁻¹ * b ∈ A ⊓ subspaceStabilizer ρ I :=
    ⟨A.mul_mem (A.inv_mem c.property) b.property, (subspace_map_eq_iff ρ I _).mp he⟩
  rw [hstab, Subgroup.mem_bot] at hm
  apply Subtype.ext
  exact (inv_mul_eq_one.mp hm).symm

/-- The actual orbit of a subspace, as the range of its image map. -/
def subspaceOrbit (A : Subgroup G) (I : Submodule (ZMod 2) V) :
    Set (Submodule (ZMod 2) V) := Set.range (fun b : A => I.map (ρ b))

/-- A regular orbit has the order of the acting subgroup. -/
theorem card_subspaceOrbit {A : Subgroup G} {I : Submodule (ZMod 2) V}
    (hstab : A ⊓ subspaceStabilizer ρ I = ⊥) :
    Nat.card (subspaceOrbit ρ A I) = Nat.card A :=
  Nat.card_range_of_injective (subspace_orbitMap_injective ρ hstab)

/-- Normalizers transport invariant subspaces to invariant subspaces. -/
theorem map_subspace_invariant_of_mem_normalizer {X : Subgroup G}
    {I : Submodule (ZMod 2) V} (hI : X ≤ subspaceStabilizer ρ I)
    {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    X ≤ subspaceStabilizer ρ (I.map (ρ g)) := by
  apply le_subspaceStabilizer
  rintro x hx _ ⟨i, hi, rfl⟩
  have hy : g⁻¹ * x * g ∈ X := by
    simpa only [inv_inv] using
      ((Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (X : Set G)).inv_mem hg)) x).mp hx
  refine ⟨ρ (g⁻¹ * x * g) i, (hI hy i).2 hi, ?_⟩
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left]

/-- Formation of quotient images commutes with the normalizer action. -/
theorem quotientImage_map_normalizer (X : Subgroup G)
    (I : Submodule (ZMod 2) V) (g : Subgroup.normalizer (X : Set G)) :
    (I.map (ρ g)).map (fixedSpace ρ X).mkQ =
      (I.map (fixedSpace ρ X).mkQ).map (normalizerQuotientRepresentation ρ X g) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  rfl

/-- An X-invariant space has an X-invariant image in V/C_V(X). -/
theorem quotientImage_invariant {X : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : X ≤ subspaceStabilizer ρ I) :
    X.subgroupOf (Subgroup.normalizer (X : Set G)) ≤
      subspaceStabilizer (normalizerQuotientRepresentation ρ X)
        (I.map (fixedSpace ρ X).mkQ) := by
  apply le_subspaceStabilizer
  rintro x hx _ ⟨i, hi, rfl⟩
  exact ⟨ρ x i, (hI hx i).2 hi, rfl⟩

/-- If A fixes D, disjointness from one member of an A-orbit gives disjointness
from every member. -/
theorem disjoint_map_of_le_fixedSpace {A : Subgroup G} {D I : Submodule (ZMod 2) V}
    (hD : D ≤ fixedSpace ρ A) (hDI : Disjoint D I) {b : G} (hb : b ∈ A) :
    Disjoint D (I.map (ρ b)) := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro v hv
  obtain ⟨i, hi, he⟩ := hv.2
  have hd : v ∈ D := hv.1
  have hbi : ρ b⁻¹ v = v := hD hd ⟨b⁻¹, A.inv_mem hb⟩
  have hiv : i = v := by
    have hh := congrArg (ρ b⁻¹) he
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply, hbi] using hh
  have hm : v ∈ D ⊓ I := ⟨hd, hiv ▸ hi⟩
  rwa [hDI.eq_bot] at hm

/-- A fixed subspace misses a space which is disjoint from one of its translates. -/
theorem disjoint_of_le_fixedSpace_of_disjoint_map {A : Subgroup G}
    {D I : Submodule (ZMod 2) V} (hD : D ≤ fixedSpace ρ A)
    {a : G} (ha : a ∈ A) (hI : Disjoint I (I.map (ρ a))) : Disjoint D I := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro v hv
  have hd : v ∈ D := hv.1
  have hi : v ∈ I := hv.2
  have hai : v ∈ I.map (ρ a) := ⟨v, hi, hD hd ⟨a, ha⟩⟩
  have hm : v ∈ I ⊓ I.map (ρ a) := ⟨hi, hai⟩
  rwa [hI.eq_bot] at hm

/-- The missing part of a partition into invariant subspaces is invariant. -/
theorem subspaceStabilizer_of_partition {ι : Type*} {X : Subgroup G}
    (U : ι → Submodule (ZMod 2) V) (D : Submodule (ZMod 2) V)
    (hU : ∀ i, X ≤ subspaceStabilizer ρ (U i))
    (hdis : ∀ i, Disjoint D (U i))
    (hcover : ∀ v : V, v ≠ 0 → v ∈ D ∨ ∃ i, v ∈ U i) :
    X ≤ subspaceStabilizer ρ D := by
  apply le_subspaceStabilizer
  intro x hx d hd
  by_cases hz : ρ x d = 0
  · rw [hz]
    exact D.zero_mem
  rcases hcover (ρ x d) hz with h | ⟨i, hi⟩
  · exact h
  · have hdi : d ∈ U i := (hU i hx d).mp hi
    have hd0 : d = 0 := by
      have : d ∈ D ⊓ U i := ⟨hd, hdi⟩
      rwa [(hdis i).eq_bot] at this
    exact (hz (by rw [hd0, map_zero])).elim
/-- The offender inequality gives the lower bound needed for orbit counting. -/
theorem IsBestOffender.two_pow_le_card_of_le_fixedCodim [Finite G]
    [FiniteDimensional (ZMod 2) V] {A : Subgroup G} (hA : IsBestOffender ρ A)
    {n : ℕ} (hn : n ≤ fixedCodim ρ A) : 2 ^ n ≤ Nat.card A := by
  rw [hA.1.card_eq_two_pow_rank]
  exact Nat.pow_le_pow_right (by decide) (hn.trans (hA.isOffender ρ).2)

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem quotientDiagonal_disjoint_orbit {X A : Subgroup G}
    {I : Submodule (ZMod 2) V} {a : G}
    (haA : a ∈ A) (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (hXA : ⁅X, A⁆ = X)
    (ha : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v) (b : A) :
    Disjoint ((diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ)
      ((I.map (ρ b)).map (fixedSpace ρ X).mkQ) := by
  let N := Subgroup.normalizer (X : Set G)
  let σ := normalizerQuotientRepresentation ρ X
  let D := (diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ
  have hAN : A ≤ N := Subgroup.le_normalizer_iff_commutator_le_left.mpr hXA.le
  have hD : D ≤ fixedSpace σ (A.subgroupOf N) := by
    rintro _ ⟨d, ⟨i, hi, rfl⟩, rfl⟩ c
    change (fixedSpace ρ X).mkQ (ρ c.val (ρ a i - i)) = _
    rw [ha c.val c.property i]
    rfl
  have hdis : Disjoint (I.map (fixedSpace ρ X).mkQ)
      ((I.map (fixedSpace ρ X).mkQ).map (σ ⟨a, hAN haA⟩)) := by
    rw [← quotientImage_map_normalizer]
    exact IsIrrPlus.disjoint_quotientImages ρ hI hIa hne
  have hDI := disjoint_of_le_fixedSpace_of_disjoint_map σ hD
    (show (⟨a, hAN haA⟩ : N) ∈ A.subgroupOf N from haA) hdis
  rw [quotientImage_map_normalizer ρ X I ⟨b, hAN b.property⟩]
  exact disjoint_map_of_le_fixedSpace σ hD hDI
    (show (⟨b, hAN b.property⟩ : N) ∈ A.subgroupOf N from b.property)

/-- The source contradiction once counting has shown that the orbit and the
diagonal cover the nonzero quotient vectors. -/
theorem irreducibleOrbit_contradiction_of_cover {X A : Subgroup G}
    {I : Submodule (ZMod 2) V} {a : G}
    (haA : a ∈ A) (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (hXA : ⁅X, A⁆ = X)
    (ha : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v)
    (hcover : ∀ q : V ⧸ fixedSpace ρ X, q ≠ 0 →
      q ∈ (diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ ∨
        ∃ b : A, q ∈ (I.map (ρ b)).map (fixedSpace ρ X).mkQ) : False := by
  apply IsIrrPlus.quotient_diagonal_not_invariant ρ hI hIa hne hXA ha
  apply subspaceStabilizer_of_partition (normalizerQuotientRepresentation ρ X)
    (fun b : A => (I.map (ρ b)).map (fixedSpace ρ X).mkQ)
    ((diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ) _
    (quotientDiagonal_disjoint_orbit ρ haA hI hIa hne hXA ha) hcover
  intro b
  apply quotientImage_invariant
  apply map_subspace_invariant_of_mem_normalizer ρ hI.choose
  exact Subgroup.le_normalizer_iff_commutator_le_left.mpr hXA.le b.property
end Representation.BinaryOffender
