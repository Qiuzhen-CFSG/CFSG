module

public import BenderSuzuki.MatrixGroups.Unitary

/-!
# Specifying entrywise conjugation on projective SU₃

The projective group is the image of the special unitary subgroup in PGL.
We expose its natural surjection and specify entrywise conjugation using actual
special unitary representatives and the conjugation stored in the Hermitian
form. The specification uniquely determines an automorphism and forces its
square to be one. Existence and fixed-group identification are separate results.

This is the concrete graph-action interface for GLS, Volume 4, Chapter 4,
Lemma 3.4(c). In particular it does not identify a fixed subgroup before
accounting for the scalar kernel of the map into PGL.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The natural map from the special unitary group onto its projective image. -/
public def specialToProjective : J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (Matrix.ProjGenLinGroup.mk.comp J.specialSubgroup.subtype).codRestrict _
    (fun x => Subgroup.mem_map_of_mem _ x.property)

@[simp] public theorem specialToProjective_apply_val (x : J.specialSubgroup) :
    (J.specialToProjective x).val = Matrix.ProjGenLinGroup.mk x.val := by rfl

public theorem specialToProjective_surjective : Function.Surjective J.specialToProjective := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

/-- Concrete entrywise action of the stored Hermitian involution, on every
special unitary representative of a projective element. -/
@[expose] public def IsEntrywiseConjugation (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
  ∀ x : J.specialSubgroup, ∃ y : J.specialSubgroup,
    y.val.val = x.val.val.map J.conj ∧ γ (J.specialToProjective x) = J.specialToProjective y

/-- The representative formula specifies at most one projective automorphism. -/
public theorem IsEntrywiseConjugation.unique
    {γ δ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (hδ : J.IsEntrywiseConjugation δ) : γ = δ := by
  apply MulEquiv.ext
  intro b
  obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
  obtain ⟨y, hy, hγx⟩ := hγ x
  obtain ⟨z, hz, hδx⟩ := hδ x
  have hyz : y = z := Subtype.ext (Units.ext (hy.trans hz.symm))
  rw [hγx, hδx, hyz]

/-- Entrywise conjugation squares to the identity on the projective image. -/
public theorem IsEntrywiseConjugation.sq_eq_one
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) : γ ^ 2 = 1 := by
  apply MulEquiv.ext
  intro b
  obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
  obtain ⟨y, hy, hγx⟩ := hγ x
  obtain ⟨z, hz, hγy⟩ := hγ y
  have hzx : z = x := by
    apply Subtype.ext
    apply Units.ext
    rw [hz, hy]
    ext i j
    exact J.conj_involutive _
  change γ (γ (J.specialToProjective x)) = J.specialToProjective x
  rw [hγx, hγy, hzx]

end BenderSuzuki.MatrixGroups.HermitianForm
