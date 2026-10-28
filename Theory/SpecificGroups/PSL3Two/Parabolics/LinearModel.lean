module

public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum

/-!
# Linear models for the binary projective plane

The canonical map SL₃(2) → PSL₃(2) and the inclusion SL₃(2) → GL₃(2)
are isomorphisms. We retain the actual quotient map so that matrix stabilizers
can be transported to the projective group without changing their actions.
Counting ordered bases gives order 168.

These are the linear models for the rank-two residues in Aschbacher–Smith,
*The Classification of Quasithin Groups*, I.5.3–4, printed pp. 419–420.
The center calculation follows the proof in
`Theory.GroupTheory.ElementaryEightNormalizerRecognition`.
-/

namespace Matrix.PSL3Two

public abbrev SL := SpecialLinearGroup (Fin 3) (ZMod 2)
public abbrev GeneralLinear := GeneralLinearGroup (Fin 3) (ZMod 2)
public abbrev PSL := ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)

/-- The center of SL₃(2) is trivial. -/
public theorem center_eq_bot : Subgroup.center SL = ⊥ := by
  apply eq_bot_iff.mpr
  intro mat hmat
  change mat = 1
  obtain ⟨scalar, hpower, hscalar⟩ := SpecialLinearGroup.mem_center_iff.mp hmat
  have hroot : ∀ scalar : ZMod 2, scalar ^ 3 = 1 → scalar = 1 := by decide
  have hscalarOne : scalar = 1 := hroot scalar (by simpa using hpower)
  apply Subtype.ext
  simpa [hscalarOne] using hscalar.symm

/-- The actual quotient by the center. -/
@[expose] public def project : SL →* PSL := QuotientGroup.mk' _

public theorem project_injective : Function.Injective project := by
  rw [← MonoidHom.ker_eq_bot_iff, project, QuotientGroup.ker_mk', center_eq_bot]

public theorem project_surjective : Function.Surjective project :=
  QuotientGroup.mk'_surjective _

/-- The canonical projection is an isomorphism. -/
public noncomputable def equiv : SL ≃* PSL :=
  MulEquiv.ofBijective project ⟨project_injective, project_surjective⟩

@[simp] public theorem equiv_apply (g : SL) : equiv g = project g := by
  unfold equiv
  rfl

/-- Every invertible binary matrix has determinant one. -/
public theorem toGL_surjective :
    Function.Surjective (SpecialLinearGroup.toGL : SL →* GeneralLinear) := by
  intro mat
  have hunits : ∀ unit : (ZMod 2)ˣ, unit = 1 := by decide
  have hdet : Matrix.det (mat : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 :=
    congrArg Units.val (hunits (GeneralLinearGroup.det mat))
  exact ⟨⟨mat, hdet⟩, Units.ext rfl⟩

/-- The inclusion of SL₃(2) into GL₃(2) is an isomorphism. -/
public noncomputable def equivGL : SL ≃* GeneralLinear :=
  MulEquiv.ofBijective SpecialLinearGroup.toGL
    ⟨SpecialLinearGroup.toGL_injective, toGL_surjective⟩

@[simp] public theorem equivGL_apply (g : SL) : equivGL g = SpecialLinearGroup.toGL g := by
  unfold equivGL
  rfl

public theorem card_PSL : Nat.card PSL = 168 := by
  rw [← Nat.card_congr equiv.toEquiv, card_SL]

/-- Every Sylow two-subgroup of PSL₃(2) has order eight. -/
public theorem card_sylow_two (S : Sylow 2 PSL) : Nat.card S = 8 := by
  rw [S.card_eq_multiplicity, card_PSL]
  decide +kernel

end Matrix.PSL3Two
