module
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionAlternatingQuotient.PermutationData
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords
public import Theory.GroupAction.PermutationLiftHom
public import Mathlib.Logic.Equiv.Set

/-!
# Matrix-pair certificates and eleven distinct stars

A family of 55 distinct matrices, permuted by conjugation according to the
unordered-pair actions of `PermutationData`, gives eleven distinct invariant
stars. Conjugation acts on actual matrices, and each star is a set of matrices,
so the resulting action will factor through the concrete matrix group itself.
Only injectivity and two families of matrix multiplication identities are
required; idempotence, subgroup orders and the abstract double cover are unused.

`PairOrbitCertificate` is an explicit outstanding finite-certificate interface.
Candidate matrices and reproducible discovery are in `source/`. They are not
asserted to satisfy the interface in this module.

Source: GLS3 section 5.3, Lyons involution table, printed p.278; the exact
ATLAS matrices and words are retained in `../Atlas111Source/` and
`../Atlas111InvolutionSource/`.
-/

namespace Lyons.SimplicityCertificate.AlternatingQuotient

/-- The finite matrix obligations for the action on unordered pairs. -/
public structure PairOrbitCertificate where
  matrix : Fin 55 → AtlasMatrix
  injective : Function.Injective matrix
  map_A : ∀ k, matrixRepresentation involutionLocalA * matrix k =
    matrix (pairA k) * matrixRepresentation involutionLocalA
  map_B : ∀ k, matrixRepresentation involutionLocalB * matrix k =
    matrix (pairB k) * matrixRepresentation involutionLocalB

private def conjugate {G M : Type*} [Group G] [Monoid M]
    (ρ : G →* M) (g : G) (x : M) : M := ρ g * x * ρ g⁻¹

private theorem conjugate_one {G M : Type*} [Group G] [Monoid M]
    (ρ : G →* M) (x : M) : conjugate ρ 1 x = x := by
  simp [conjugate]

private theorem conjugate_mul {G M : Type*} [Group G] [Monoid M]
    (ρ : G →* M) (g h : G) (x : M) :
    conjugate ρ (g * h) x = conjugate ρ g (conjugate ρ h x) := by
  simp only [conjugate, map_mul, mul_inv_rev, mul_assoc]

private theorem conjugate_inv {G M : Type*} [Group G] [Monoid M]
    (ρ : G →* M) (g : G) (x : M) : conjugate ρ g⁻¹ (conjugate ρ g x) = x := by
  rw [← conjugate_mul, inv_mul_cancel, conjugate_one]

private def representedConjugation {G M : Type*} [Group G] [Monoid M]
    (ρ : G →* M) : G →* Equiv.Perm M where
  toFun g :=
    { toFun := conjugate ρ g
      invFun := conjugate ρ g⁻¹
      left_inv := conjugate_inv ρ g
      right_inv := fun M => by simpa only [inv_inv] using conjugate_inv ρ g⁻¹ M }
  map_one' := Equiv.ext (conjugate_one ρ)
  map_mul' g h := Equiv.ext (conjugate_mul ρ g h)

private def setsHom {Y : Type*} : Equiv.Perm Y →* Equiv.Perm (Set Y) where
  toFun e := Equiv.Set.congr e
  map_one' := by ext S y; simp
  map_mul' e f := by
    ext S y
    simp only [Equiv.Set.congr_apply, Equiv.Perm.mul_apply, Set.image_image]
    rfl

/-- Conjugation by the literal matrix representation, acting on sets of matrices. -/
public def matrixSetAction : LyonsGroup →* Equiv.Perm (Set AtlasMatrix) :=
  setsHom.comp (representedConjugation matrixRepresentation)

/-- The star of a letter consists of the ten matrices on pairs incident to it. -/
@[expose] public def star (C : PairOrbitCertificate) (i : Fin 11) : Set AtlasMatrix :=
  {M | ∃ k, incident i k ∧ C.matrix k = M}

public theorem star_injective (C : PairOrbitCertificate) : Function.Injective (star C) := by
  intro i j hij
  by_contra h
  obtain ⟨k, hki, hkj⟩ := incidence_separates i j h
  have hm : C.matrix k ∈ star C i := ⟨k, hki, rfl⟩
  rw [hij] at hm
  obtain ⟨l, hlj, hlk⟩ := hm
  exact hkj (C.injective hlk ▸ hlj)

private theorem star_image (C : PairOrbitCertificate) (f : AtlasMatrix → AtlasMatrix)
    (p : Equiv.Perm (Fin 11)) (q : Equiv.Perm (Fin 55))
    (hi : ∀ i k, incident (p i) (q k) ↔ incident i k)
    (hf : ∀ k, f (C.matrix k) = C.matrix (q k)) (i : Fin 11) :
    f '' star C i = star C (p i) := by
  ext M
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨q k, (hi i k).mpr hk, (hf k).symm⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨C.matrix (q.symm k), ⟨q.symm k, ?_, rfl⟩, ?_⟩
    · apply (hi i (q.symm k)).mp
      simpa only [Equiv.apply_symm_apply] using hk
    · rw [hf, Equiv.apply_symm_apply]

private theorem conjugate_of_intertwining (g : LyonsGroup) (M N : AtlasMatrix)
    (h : matrixRepresentation g * M = N * matrixRepresentation g) :
    conjugate matrixRepresentation g M = N := by
  rw [conjugate, h, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

public theorem star_actionA (C : PairOrbitCertificate) (i : Fin 11) :
    matrixSetAction involutionLocalA (star C i) = star C (letterA i) :=
  star_image C _ letterA pairA incident_pairA
    (fun k => conjugate_of_intertwining _ _ _ (C.map_A k)) i

public theorem star_actionB (C : PairOrbitCertificate) (i : Fin 11) :
    matrixSetAction involutionLocalB (star C i) = star C (letterB i) :=
  star_image C _ letterB pairB incident_pairB
    (fun k => conjugate_of_intertwining _ _ _ (C.map_B k)) i

end Lyons.SimplicityCertificate.AlternatingQuotient
