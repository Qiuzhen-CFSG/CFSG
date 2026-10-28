module

public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.Source
public import Theory.Representation.ScalarDescent

/-!
# Descent of the cubic displacement calculation in H.4.7

Scalar extension preserves displacement rank, and restriction from the actual
Schur field multiplies it by the Schur degree. The existing five-word
classification excludes the two natural words when the binary dimension is
not nine. Absolute ranks six, six and forty-two on the remaining three words
therefore give binary ranks twelve, twelve and forty-two.

The last theorem transports this conditional calculation through the literal
SL₃ cover of F*(M), retaining the original representation and component actor.
The absolute word ranks are explicit obligations, not established here.

Source: Aschbacher–Smith H.4.7, refs/quasithin.pdf, printed pp.382–383.
-/

public section

set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct MonoidAlgebra MatrixGroups
open Representation Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
  (SchurField SplittingField)
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum

private theorem finrank_baseChange_submodule {k K U : Type*}
    [Field k] [Field K] [Algebra k K] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] (P : Submodule k U) :
    Module.finrank K (P.baseChange K) = Module.finrank k P := by
  let f := Submodule.toBaseChange K P
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg Subtype.val h
    change P.subtype.baseChange K x = P.subtype.baseChange K y at hh
    apply Module.Flat.lTensor_preserves_injective_linearMap P.subtype Subtype.val_injective
    simpa only [LinearMap.baseChange_eq_ltensor] using hh
  let e := LinearEquiv.ofBijective f ⟨hf, Submodule.toBaseChange_surjective K P⟩
  rw [← e.finrank_eq]
  exact Module.finrank_baseChange

private theorem finrank_range_baseChange {k K U : Type*}
    [Field k] [Field K] [Algebra k K] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] (f : Module.End k U) :
    Module.finrank K (f.baseChange K).range = Module.finrank k f.range := by
  have hk : Module.finrank K (f.baseChange K).ker = Module.finrank k f.ker := by
    rw [← f.baseChange_ker_eq]
    exact finrank_baseChange_submodule _
  have h1 := (f.baseChange K).finrank_range_add_finrank_ker
  have h2 := f.finrank_range_add_finrank_ker
  rw [hk, Module.finrank_baseChange] at h1
  omega

private theorem finrank_range_intertwined {k U W : Type*} [Field k]
    [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    (e : U ≃ₗ[k] W) (f : Module.End k U) (h : Module.End k W)
    (he : ∀ x, e (f x) = h (e x)) :
    Module.finrank k f.range = Module.finrank k h.range := by
  have hm : f.range.map e.toLinearMap = h.range := by
    ext y
    constructor
    · rintro ⟨x, ⟨z,rfl⟩,rfl⟩
      exact ⟨e z,(he z).symm⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨z,rfl⟩ := e.surjective x
      exact ⟨f z, ⟨z,rfl⟩, he z⟩
  rw [← hm, e.finrank_map_eq]

variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(3,F) V) [IsIrreducible ρ]

/-- Displacement on the original binary space is the Schur degree times
the displacement on its actual absolutely irreducible scalar extension. -/
theorem binary_displacement_eq_schurDegree_mul (g : SL(3,F)) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) = schurDegree 2 ρ *
      Module.finrank (SplittingField ρ)
        (LinearMap.range (extendScalars (SplittingField ρ) ρ.endFieldRep g - 1)) := by
  let E := SchurField ρ
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  have ht : Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ.endFieldRep g - 1)) := by
    have h := finrank_range_intertwined ρ.asModuleEquiv
      ((ρ.endFieldRep g - 1).restrictScalars (ZMod 2)) (ρ g - 1) (fun v => by
        simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply,
          Module.End.one_apply, map_sub, endFieldRep_apply, LinearEquiv.apply_symm_apply])
    exact h.symm
  rw [ht, ← Module.finrank_mul_finrank (ZMod 2) E]
  congr 1
  rw [extendScalars_apply, ← LinearMap.baseChange_one E ρ.asModule,
    ← LinearMap.baseChange_sub]
  exact (finrank_range_baseChange _).symm

private theorem displacement_equiv {k G U W : Type*} [Field k] [Group G]
    [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    {σ : Representation k G U} {τ : Representation k G W} (e : σ.Equiv τ) (g : G) :
    Module.finrank k (LinearMap.range (σ g - 1)) =
      Module.finrank k (LinearMap.range (τ g - 1)) := by
  apply finrank_range_intertwined e.toLinearEquiv
  intro v
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  exact congrArg (fun w => w - e.toLinearEquiv v)
    (Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap g v)

open CFSG.Quasithin.ChapterH.Section01To04.L3Four
variable [Finite F] [CharP F 2]

/-- The three absolute adjoint-word calculations give the exact binary
displacement alternatives. This reduction does not supply those calculations. -/
theorem binary_displacement_of_word_ranks (hcard : Nat.card F = 4)
    (hcenter : Subgroup.center SL(3,F) ≤ ρ.ker) (hact : ∃ g, ρ g ≠ 1)
    (hdim : Module.finrank (ZMod 2) V ≠ 9) (g : SL(3,F))
    (hcalc : ∀ ι : F →+* SplittingField ρ,
      Module.finrank (SplittingField ρ)
        (LinearMap.range (wordRep ι [.adjoint,.trivial] g - 1)) = 6 ∧
      Module.finrank (SplittingField ρ)
        (LinearMap.range (wordRep ι [.trivial,.adjoint] g - 1)) = 6 ∧
      Module.finrank (SplittingField ρ)
        (LinearMap.range (wordRep ι [.adjoint,.adjoint] g - 1)) = 42) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) = 12 ∨
      Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) = 42 := by
  obtain ⟨ι,b,c,hbc,⟨e⟩,hs,hd⟩ := exists_nontrivial_binary_pair_model ρ hcard hcenter hact
  have hr := binary_displacement_eq_schurDegree_mul ρ g
  rw [displacement_equiv e g, hs] at hr
  rcases hbc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact (hdim (by simpa [wordDegree, Factor.dimension] using hd)).elim
  · exact (hdim (by simpa [wordDegree, Factor.dimension] using hd)).elim
  · exact Or.inl (by simpa [(hcalc ι).2.1] using hr)
  · exact Or.inl (by simpa [(hcalc ι).1] using hr)
  · exact Or.inr (by simpa [(hcalc ι).2.2] using hr)

open Theory.GroupTheory
variable {M : Type*} [Group M]

/-- Apply the word calculations through the literal cover of the generalized
Fitting subgroup. The absolute word ranks remain explicit premises. -/
theorem source_displacement_of_word_ranks (hcard : Nat.card F = 4)
    (e : PSL(3,F) ≃* generalizedFitting M) (σ : Representation (ZMod 2) M V)
    [IsIrreducible (σ.comp (generalizedFitting M).subtype)] (hσ : Function.Injective σ)
    (hdim : Module.finrank (ZMod 2) V ≠ 9)
    (hcalc : ∀ (g : SL(3,F)),
      orderOf (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) = 3 →
      ∀ ι : F →+* SplittingField (coverRep e σ),
      Module.finrank (SplittingField (coverRep e σ))
        (LinearMap.range (wordRep ι [.adjoint,.trivial] g - 1)) = 6 ∧
      Module.finrank (SplittingField (coverRep e σ))
        (LinearMap.range (wordRep ι [.trivial,.adjoint] g - 1)) = 6 ∧
      Module.finrank (SplittingField (coverRep e σ))
        (LinearMap.range (wordRep ι [.adjoint,.adjoint] g - 1)) = 42)
    (x : generalizedFitting M) (hx : orderOf x = 3) :
    12 ≤ Module.finrank (ZMod 2) (LinearMap.range (σ (x : M) - 1)) := by
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) (e.symm x)
  have horder : orderOf (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) = 3 := by
    rw [hg]
    exact (orderOf_injective e.symm.toMonoidHom e.symm.injective x).trans hx
  have hcov : componentCover e g = (x : M) := by
    change ((e (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) : generalizedFitting M) : M) = _
    rw [hg, e.apply_symm_apply]
  have hr := binary_displacement_of_word_ranks (coverRep e σ) hcard
    (le_of_eq (coverRep_ker e σ hσ).symm) (coverRep_nontrivial e σ hσ)
    hdim g (hcalc g horder)
  have he : coverRep e σ g = σ (x : M) := by
    change σ (componentCover e g) = _
    rw [hcov]
  rw [he] at hr
  omega


end CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum
