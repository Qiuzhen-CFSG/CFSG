module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Frames
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Frame stabilizers and actual unitary Borels

The torus defined in `OddTorusNormalizer.Frames` is exactly the pointwise
stabilizer of the three projective lines of its orthonormal basis. A group
permuting these lines therefore normalizes that literal torus. This argument
also descends through the actual special-to-projective map.

The no-Borel conditions below use stabilizers of isotropic projective lines
under the natural matrix actions. They agree under full preimage from PSU₃
to SU₃. No numerical torus structure or preserved-frame existence is assumed
in these definitions or proved by the normalization lemmas.

Source: GLS4, Chapter 4, Lemma 3.11(a), `refs/KGroup/GLS4/Chapter4.tex`,
lines 585–603. Construction of an invariant frame is a separate obligation.
-/

@[expose] public section

open Matrix Subgroup
open scoped Pointwise LinearAlgebra.Projectivization
namespace UnitaryThree.OddTorusNormalizer
open BenderSuzuki.MatrixGroups
variable {E : Type*} [Field E]

/-- The projective line spanned by a standard basis vector. -/
def coordinateLine (i : Fin 3) : ℙ E (Fin 3 → E) :=
  Projectivization.mk E (Pi.single i 1) (by
    intro h
    have := congrFun h i
    simp at this)

/-- The three actual projective column lines of the orthonormal basis. -/
def frameLines {J : HermitianForm 3 E} (P : OrthogonalFrame J) :
    Set (ℙ E (Fin 3 → E)) :=
  P.val • Set.range (coordinateLine (E := E))

/-- The special-unitary setwise stabilizer of the three frame lines. -/
def specialFrameStabilizer (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Subgroup J.specialSubgroup := MulAction.stabilizer J.specialSubgroup (frameLines P)

/-- The projective-unitary setwise stabilizer of the same three lines. -/
def projectiveFrameStabilizer (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (frameLines P)

private theorem diagonal_range_eq_fixing :
    (diagonalHom (E := E)).range =
      fixingSubgroup (GL (Fin 3) E) (Set.range (coordinateLine (E := E))) := by
  classical
  ext x
  rw [mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨a, rfl⟩ l ⟨i, rfl⟩
    rw [coordinateLine, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    refine ⟨a i, ?_⟩
    change (a i : E) • Pi.single i 1 = (diagonalHom a).val *ᵥ Pi.single i 1
    ext j
    by_cases hj : j = i
    · subst j
      simp [diagonalHom]
    · simp [diagonalHom, hj]
  · intro hx
    have hi (i : Fin 3) : ∃ a : Eˣ, a • Pi.single i 1 = x.val *ᵥ Pi.single i 1 := by
      have h := hx _ ⟨i, rfl⟩
      rw [coordinateLine, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h
      exact h
    choose a ha using hi
    refine ⟨a, ?_⟩
    apply Units.ext
    ext i j
    have h := congrFun (ha j) i
    by_cases hij : i = j
    · subst j
      simpa [diagonalHom, Matrix.mulVec_single_one, Units.smul_def] using h
    · simpa [diagonalHom, Matrix.mulVec_single_one, Pi.single_apply,
        Matrix.diagonal_apply, hij, Units.smul_def] using h

/-- The literal diagonal torus fixes exactly each of the three frame lines. -/
theorem specialFrameTorus_eq_fixing (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    specialFrameTorus J P = fixingSubgroup J.specialSubgroup (frameLines P) := by
  ext x
  change (P.val⁻¹ * x.val * P.val ∈ (diagonalHom (E := E)).range) ↔ _
  rw [diagonal_range_eq_fixing, mem_fixingSubgroup_iff, mem_fixingSubgroup_iff]
  constructor
  · intro h l hl
    obtain ⟨z, hz, rfl⟩ := hl
    change x.val • (P.val • z) = P.val • z
    have hh := congrArg (fun z : ℙ E (Fin 3 → E) => P.val • z) (h z hz)
    simpa only [mul_smul, smul_inv_smul] using hh
  · intro h z hz
    have hh := h (P.val • z) (Set.smul_mem_smul_set hz)
    change x.val • (P.val • z) = P.val • z at hh
    rw [mul_smul, mul_smul, hh, inv_smul_smul]

private theorem stabilizer_le_normalizer_fixing {G α : Type*} [Group G]
    [MulAction G α] (s : Set α) :
    MulAction.stabilizer G s ≤ normalizer (fixingSubgroup G s) := by
  rw [le_normalizer_iff]
  intro g hg k hk
  rw [mem_fixingSubgroup_iff] at hk ⊢
  intro z hz
  have hgi : g⁻¹ • s = s :=
    MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer G s).inv_mem hg)
  have hgz : g⁻¹ • z ∈ s := by
    rw [← hgi]
    exact Set.smul_mem_smul_set hz
  rw [mul_smul, mul_smul, hk _ hgz, smul_inv_smul]

/-- Permuting the three frame lines normalizes the literal special torus. -/
theorem specialFrameStabilizer_le_normalizer (J : HermitianForm 3 E)
    (P : OrthogonalFrame J) :
    specialFrameStabilizer J P ≤ normalizer (specialFrameTorus J P) := by
  rw [specialFrameTorus_eq_fixing]
  exact stabilizer_le_normalizer_fixing (frameLines P)

/-- The actual projection preserves the natural action on projective lines. -/
theorem specialToProjective_smul (J : HermitianForm 3 E) (x : J.specialSubgroup)
    (l : ℙ E (Fin 3 → E)) : J.specialToProjective x • l = x • l := by
  induction l using Projectivization.ind with
  | _ v hv =>
    change (J.specialToProjective x).val • Projectivization.mk E v hv =
      x.val • Projectivization.mk E v hv
    rw [J.specialToProjective_apply_val]
    rfl

/-- Frame preservation agrees under full preimage along SU₃ → PSU₃. -/
theorem specialFrameStabilizer_eq_comap (J : HermitianForm 3 E)
    (P : OrthogonalFrame J) :
    specialFrameStabilizer J P =
      (projectiveFrameStabilizer J P).comap J.specialToProjective := by
  ext x
  change x • frameLines P = frameLines P ↔
    J.specialToProjective x • frameLines P = frameLines P
  have he : x • frameLines P = J.specialToProjective x • frameLines P := by
    apply Set.image_congr
    intro l _
    exact (specialToProjective_smul J x l).symm
  rw [he]

/-- Permuting the three lines normalizes the actual projective torus image. -/
theorem projectiveFrameStabilizer_le_normalizer (J : HermitianForm 3 E)
    (P : OrthogonalFrame J) :
    projectiveFrameStabilizer J P ≤ normalizer (projectiveFrameTorus J P) := by
  intro x hx
  obtain ⟨y, rfl⟩ := J.specialToProjective_surjective x
  apply le_normalizer_map J.specialToProjective
  apply mem_map_of_mem
  apply specialFrameStabilizer_le_normalizer
  rwa [specialFrameStabilizer_eq_comap]

/-- Isotropy in the actual Hermitian form, expressed on projective lines. -/
def IsIsotropicLine (J : HermitianForm 3 E) (l : ℙ E (Fin 3 → E)) : Prop :=
  ∃ (v : Fin 3 → E) (hv : v ≠ 0),
    l = Projectivization.mk E v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0

/-- Exclusion from every genuine isotropic-line stabilizer in SU₃. -/
def SpecialNoBorel (J : HermitianForm 3 E) (H : Subgroup J.specialSubgroup) : Prop :=
  ∀ l : ℙ E (Fin 3 → E), IsIsotropicLine J l →
    ¬ H ≤ MulAction.stabilizer J.specialSubgroup l

/-- Exclusion from every genuine isotropic-line stabilizer in PSU₃. -/
def ProjectiveNoBorel (J : HermitianForm 3 E)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
  ∀ l : ℙ E (Fin 3 → E), IsIsotropicLine J l →
    ¬ H ≤ MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) l

/-- No-Borel exclusion is preserved and reflected by the actual projective map. -/
theorem specialNoBorel_comap_iff (J : HermitianForm 3 E)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    SpecialNoBorel J (H.comap J.specialToProjective) ↔ ProjectiveNoBorel J H := by
  have he (l : ℙ E (Fin 3 → E)) :
      MulAction.stabilizer J.specialSubgroup l =
        (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) l).comap
          J.specialToProjective := by
    ext x
    change x • l = l ↔ J.specialToProjective x • l = l
    rw [specialToProjective_smul]
  unfold SpecialNoBorel ProjectiveNoBorel
  simp_rw [he, Subgroup.comap_le_comap_of_surjective J.specialToProjective_surjective]

end UnitaryThree.OddTorusNormalizer
