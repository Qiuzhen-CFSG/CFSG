module
public import Theory.Representation.SL3.AdjointCubicCentralizer.Projective
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.RestrictedFactors
public import Theory.Representation.PSL3Four.SmallDegree
public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.SL3.AdjointCubicCentralizer.Faithful
public import Theory.Representation.ScalarRestrictionLargeConstituent
/-!
# The adjoint PSL₃(4) module over the prime field

The adjoint action is irreducible over F₄. Its fixed space is zero, so a
simple binary constituent is nontrivial and has dimension at least nine
by the proved PSL₃(4) degree gap. The total binary dimension is sixteen;
the large-constituent scalar lemma makes the restriction irreducible.

The determinant twist agrees with this action on the literal PSL₃ image,
so its PGL₃ action is also binary irreducible. The independent matrix-kernel
calculation supplies faithfulness. Thus these two hypotheses do not remove
the alternative extension in Aschbacher--Smith B.4.14, printed p.98.
The full parabolic chief-factor profile is not asserted here.
-/

open Representation Matrix
open scoped MatrixGroups
namespace Representation.SL3.AdjointCubicCentralizer
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
attribute [local instance] ZMod.algebra

/-- The ordinary adjoint action through the actual PSL-to-PGL inclusion. -/
def projectiveSpecialAdjoint : Representation F PSL(3,F) (TraceZero F) :=
  (projectiveAdjoint F).comp Matrix.ProjectiveSpecialLinearGroup.toPGL

omit [Finite F] in
private theorem special_irreducible : IsIrreducible (projectiveSpecialAdjoint F) := by
  have h := (RepEquiv.irreducible_euqiv
    (RepEquiv.ofRepresentationEquiv (adjointRestrictionEquiv F))).mp
      (BinaryDefiningFactors.factorRep_isIrreducible (RingHom.id F) .adjoint)
  exact (irreducible_comp_surjective_iff (QuotientGroup.mk' (Subgroup.center SL(3,F)))
    (QuotientGroup.mk'_surjective _) (projectiveSpecialAdjoint F)).mp h

omit [Finite F] [CharP F 2] in
private theorem dim_eight : Module.finrank F (TraceZero F) = 8 :=
  (matrixAdjointEquiv F).finrank_eq.symm.trans (BinaryDefiningFactors.finrank_adjointSpace F)

private theorem dim_sixteen (hF : Nat.card F = 4) :
    Module.finrank (ZMod 2) (TraceZero F) = 16 := by
  let : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  have hd : Module.finrank (ZMod 2) F = 2 := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [Nat.card_zmod,hF] at he
    exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using he.symm)
  rw [←Module.finrank_mul_finrank (ZMod 2) F (TraceZero F),hd,dim_eight]

omit [Finite F] in
private theorem fixed_eq_bot : (projectiveSpecialAdjoint F).invariants = ⊥ := by
  let ρ := projectiveSpecialAdjoint F
  let := special_irreducible F
  let W : Subrepresentation ρ :=
    { toSubmodule := ρ.invariants
      apply_mem_toSubmodule := by
        intro g v hv
        change ∀ h, ρ h (ρ g v) = ρ g v
        rw [hv g]
        exact hv }
  rcases eq_bot_or_eq_top W with hz | ht
  · exact congrArg Subrepresentation.toSubmodule hz
  · exfalso
    have htriv (g : PSL(3,F)) (v : TraceZero F) : ρ g v = v :=
      (ht.ge (show v ∈ (⊤ : Subrepresentation ρ) from by trivial)) g
    let : Nontrivial (TraceZero F) := Module.nontrivial_of_finrank_pos (by rw [dim_eight]; decide)
    obtain ⟨v,hv⟩ := exists_ne (0 : TraceZero F)
    let P : Subrepresentation ρ :=
      { toSubmodule := Submodule.span F {v}
        apply_mem_toSubmodule g v hv := by rw [htriv]; exact hv }
    have hd := dim_eight F
    have hpdim : Module.finrank F P.toSubmodule = 1 := by
      exact finrank_span_singleton hv
    rcases eq_bot_or_eq_top P with he | he
    · have hh := congrArg (fun A : Subrepresentation ρ => Module.finrank F A.toSubmodule) he
      change Module.finrank F P.toSubmodule = Module.finrank F (⊥ : Submodule F (TraceZero F)) at hh
      rw [finrank_bot] at hh
      omega
    · have hh := congrArg (fun A : Subrepresentation ρ => Module.finrank F A.toSubmodule) he
      change Module.finrank F P.toSubmodule = Module.finrank F (⊤ : Submodule F (TraceZero F)) at hh
      rw [finrank_top] at hh
      omega

/-- The adjoint PSL₃(4) action is irreducible even over the prime field. -/
theorem projectiveSpecialAdjoint_binary_irreducible (hF : Nat.card F = 4) :
    IsIrreducible (restrictScalars (k := ZMod 2) (projectiveSpecialAdjoint F)) := by
  let ρ := projectiveSpecialAdjoint F
  let τ := restrictScalars (k := ZMod 2) ρ
  let : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  let : Nontrivial (TraceZero F) := Module.nontrivial_of_finrank_pos (by rw [dim_eight]; decide)
  let : ρ.IsIrreducible := special_irreducible F
  obtain ⟨W,hW⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional τ
  let := hW
  have hmove : ∃ g, W.toRepresentation g ≠ 1 := by
    by_contra! hh
    let : Nontrivial W.toSubmodule := Subrepresentation.irreducible_module_nontrivial W.toRepresentation
    obtain ⟨w,hw⟩ := exists_ne (0 : W.toSubmodule)
    have hf : w.val ∈ ρ.invariants := fun g =>
      congrArg Subtype.val (LinearMap.congr_fun (hh g) w)
    rw [fixed_eq_bot] at hf
    exact hw (Subtype.ext hf)
  have hdim := Representation.PSL3Four.finrank_ge_nine hF W.toRepresentation hmove
  apply irreducible_restrictScalars_of_large_constituent ρ W
  rw [dim_sixteen F hF]
  omega
end
end Representation.SL3.AdjointCubicCentralizer

namespace Representation.SL3.AdjointCubicCentralizer
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
attribute [local instance] ZMod.algebra

/-- Restriction of the determinant-twisted PGL₃(4) action to the prime field. -/
def binaryTwistedAdjoint (hF : Nat.card F = 4) :
    Representation (ZMod 2) (Matrix.ProjGenLinGroup (Fin 3) F) (TraceZero F) :=
  restrictScalars (k := ZMod 2) (projectiveTwistedAdjoint F (units_cube_of_card_four F hF))

/-- The determinant-twisted extension satisfies the binary irreducibility
hypothesis, through its literal PSL₃ restriction. -/
theorem binaryTwistedAdjoint_irreducible (hF : Nat.card F = 4) :
    (binaryTwistedAdjoint F hF).IsIrreducible := by
  let ρ := binaryTwistedAdjoint F hF
  let q := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 3) (R := F)
  have he : ρ.comp q = restrictScalars (k := ZMod 2) (projectiveSpecialAdjoint F) := by
    apply MonoidHom.ext
    intro g
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) g
    exact congrArg (fun f : Module.End F (TraceZero F) => f.restrictScalars (ZMod 2))
      (twistedAdjoint_specialLinear F a)
  have hi : IsIrreducible (ρ.comp q) := he ▸ projectiveSpecialAdjoint_binary_irreducible F hF
  let := hi
  let : Nontrivial (TraceZero F) := Subrepresentation.irreducible_module_nontrivial (ρ.comp q)
  rw [IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun S => ?_⟩
  let U : Subrepresentation (ρ.comp q) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g := S.apply_mem_toSubmodule (q g) }
  rcases eq_bot_or_eq_top U with h | h
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun A : Subrepresentation (ρ.comp q) => A.toSubmodule) h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun A : Subrepresentation (ρ.comp q) => A.toSubmodule) h)
/-- Restricting scalars preserves the already proved faithful action. -/
theorem binaryTwistedAdjoint_injective (hF : Nat.card F = 4) :
    Function.Injective (binaryTwistedAdjoint F hF) := by
  intro g h he
  apply projectiveTwistedAdjoint_injective F (units_cube_of_card_four F hF)
  apply LinearMap.ext
  intro X
  exact LinearMap.congr_fun he X

end
end Representation.SL3.AdjointCubicCentralizer
