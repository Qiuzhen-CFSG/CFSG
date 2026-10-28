module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.Geometry
public import Theory.Representation.GeneralLinearNatural

/-!
# Common eigenlines of a special unitary subgroup

The common eigenlines are the actual projective lines fixed by every element
of the subgroup. Its normalizer permutes this set. Consequently, identifying
this set with the three lines of an orthonormal basis places the subgroup and
any normalizing element in the normalizer of the literal frame torus.

`IsCommonEigenbasis` is an intermediate spectral condition over the original
coefficient field. It assumes neither orthogonality nor invariance under a
normalizing element. The no-Borel hypothesis makes every common eigenline
anisotropic. Constructing an eigenbasis and turning all these lines into an
orthogonal frame are separate obligations.

Source: GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise LinearAlgebra.Projectivization
namespace UnitaryThree.OddTorusNormalizer.AbelianFrame
variable {E : Type*} [Field E]

/-- The actual natural representation of the special unitary matrix group. -/
@[expose] noncomputable def specialNatural (J : HermitianForm 3 E) :
    Representation E J.specialSubgroup (Fin 3 → E) :=
  (Representation.generalLinearNatural 3).comp J.specialSubgroup.subtype

/-- Faithfulness retains the literal special-unitary matrices. -/
theorem specialNatural_injective (J : HermitianForm 3 E) :
    Function.Injective (specialNatural J) :=
  (Representation.generalLinearNatural_injective 3).comp Subtype.val_injective

/-- All projective lines fixed by the whole subgroup. -/
@[expose] def commonEigenlines (J : HermitianForm 3 E) (H : Subgroup J.specialSubgroup) :
    Set (ℙ E (Fin 3 → E)) := {l | H ≤ MulAction.stabilizer J.specialSubgroup l}

/-- An actual basis over `E` whose individual lines are fixed by the subgroup. -/
@[expose] def IsCommonEigenbasis (J : HermitianForm 3 E) (H : Subgroup J.specialSubgroup)
    (b : Module.Basis (Fin 3) E (Fin 3 → E)) : Prop :=
  ∀ i, Projectivization.mk E (b i) (b.ne_zero i) ∈ commonEigenlines J H

private theorem smul_commonEigenline (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) {x : J.specialSubgroup}
    (hx : x ∈ normalizer H) {l : ℙ E (Fin 3 → E)}
    (hl : l ∈ commonEigenlines J H) : x • l ∈ commonEigenlines J H := by
  intro h hh
  have hc : x⁻¹ * h * x ∈ H := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (H : Set J.specialSubgroup)).inv_mem hx) h).mp hh
  change h • (x • l) = x • l
  have hf : (x⁻¹ * h * x) • l = l := hl hc
  calc
    h • (x • l) = x • ((x⁻¹ * h * x) • l) := by
      simp only [mul_smul, smul_inv_smul]
    _ = x • l := congrArg (fun k => x • k) hf

/-- A normalizing matrix permutes the entire set of common eigenlines. -/
theorem normalizer_le_commonEigenlines_stabilizer (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) :
    normalizer H ≤ MulAction.stabilizer J.specialSubgroup (commonEigenlines J H) := by
  intro x hx
  change x • commonEigenlines J H = commonEigenlines J H
  ext l
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact smul_commonEigenline J H hx hk
  · intro hl
    exact ⟨x⁻¹ • l, smul_commonEigenline J H ((Subgroup.normalizer (H : Set J.specialSubgroup)).inv_mem hx) hl,
      smul_inv_smul x l⟩

/-- The source no-Borel hypothesis excludes isotropy of every common eigenline. -/
theorem commonEigenline_not_isotropic (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (hB : SpecialNoBorel J H)
    {l : ℙ E (Fin 3 → E)} (hl : l ∈ commonEigenlines J H) :
    ¬ IsIsotropicLine J l := fun hi => hB l hi hl

/-- Identifying the common eigenlines as a frame supplies its actual stabilizer. -/
theorem special_frame_of_commonEigenlines (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (t : J.specialSubgroup)
    (htH : t ∈ normalizer H) (P : OrthogonalFrame J)
    (hP : commonEigenlines J H = frameLines P) :
    H ⊔ zpowers t ≤ specialFrameStabilizer J P := by
  have hle := normalizer_le_commonEigenlines_stabilizer J H
  rw [hP] at hle
  exact (sup_le H.le_normalizer (zpowers_le.mpr htH)).trans hle

/-- The canonical-frame identification supplies the literal torus-normalizer consumer. -/
theorem special_placement_of_commonEigenlines (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (t : J.specialSubgroup)
    (htH : t ∈ normalizer H) (P : OrthogonalFrame J)
    (hP : commonEigenlines J H = frameLines P) :
    H ⊔ zpowers t ≤ normalizer (specialFrameTorus J P) :=
  (special_frame_of_commonEigenlines J H t htH P hP).trans
    (specialFrameStabilizer_le_normalizer J P)
end UnitaryThree.OddTorusNormalizer.AbelianFrame
