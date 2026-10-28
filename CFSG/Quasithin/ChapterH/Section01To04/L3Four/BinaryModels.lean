module

public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.CentralCharacters
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteModels
public import Theory.Representation.SL3.BinaryDefiningFactors.FrobeniusPeriod
public import Theory.Representation.Quotient

/-!
# Binary fields of definition for the PSL₃(4) words

Extend the actual commuting endomorphism field to its algebraic closure and
apply the concrete SL₃ classification with the proved central-kernel test.
The exact Frobenius-period theorem identifies the Schur degree with the
period of the two-letter word: one for equal factors and two otherwise.
The dimension tower gives the nontrivial binary degrees 9, 16 and 64.
All model conclusions retain an actual representation equivalence; equal
dimensions alone are never used to identify a module.

Source: Aschbacher–Smith H.4.7, printed pp.382–383 of refs/quasithin.pdf;
GLS III 2.8.6, Remark 2.8.8 and 2.8.10(c). The involution estimates and the
identification with the descended Hermitian tensor remain separate steps.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
  (SchurField SplittingField)
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four
variable {F V : Type*} [Field F]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL(3,F) V) [IsIrreducible ρ]

instance schurField_charTwo : CharP (SchurField ρ) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2

private theorem scalarExtension_eq_one_iff (g : SL(3,F)) :
    extendScalars (SplittingField ρ) ρ.endFieldRep g = 1 ↔ ρ g = 1 := by
  have he : ρ.endFieldRep g = 1 ↔ ρ g = 1 := by
    constructor
    · intro h
      apply LinearMap.ext
      intro v
      have hh := congrArg (fun f : Module.End (SchurField ρ) ρ.asModule =>
        ρ.asModuleEquiv (f (ρ.asModuleEquiv.symm v))) h
      simpa only [endFieldRep_apply, LinearEquiv.apply_symm_apply, Module.End.one_apply] using hh
    · intro h
      apply LinearMap.ext
      intro v
      simp only [endFieldRep_apply, h, Module.End.one_apply, LinearEquiv.symm_apply_apply]
  rw [← he]
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    apply (Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := SchurField ρ) (B := SplittingField ρ) ρ.asModule)
    exact congrArg (fun f : Module.End (SplittingField ρ)
      (SplittingField ρ ⊗[SchurField ρ] ρ.asModule) => f (1 ⊗ₜ[SchurField ρ] v)) h
  · intro h
    rw [extendScalars_apply, h]
    exact LinearMap.baseChange_one _ _

variable [Finite F]

/-- The surviving words have Frobenius period one exactly when their factors agree. -/
theorem pair_schurDegree (hcard : Nat.card F = 4)
    (ι : F →+* SplittingField ρ) (b c : Factor)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι [b,c]))) :
    schurDegree 2 ρ = if b = c then 1 else 2 := by
  have hp := word_rotate_iff_schurDegree_dvd ρ ι [b,c]
    (by simpa using hcard) (wordRep_isIrreducible ι 2 (by simpa using hcard))
    (fun u v hu hv h => (wordRep_equiv_iff ι 2 (by simpa using hcard) u v hu hv).mp h)
    hmodel
  have hd : schurDegree 2 ρ ∣ 2 := (hp 2).mp (List.rotate_length [b,c])
  have h1 : schurDegree 2 ρ ∣ 1 ↔ b = c := by
    rw [← hp 1]
    simp only [List.rotate_cons_succ, List.rotate_zero, List.cons_append,
      List.nil_append, List.cons.injEq, and_true]
    exact ⟨fun h => h.1.symm, fun h => ⟨h.symm, h⟩⟩
  split_ifs with h
  · exact Nat.dvd_one.mp (h1.mpr h)
  · exact ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd).resolve_left
      (fun hs => h ((h1).mp (by simp [hs])))

variable [CharP F 2]

/-- Every binary irreducible central quotient has a genuine Schur-extension word model. -/
theorem exists_binary_pair_model (hcard : Nat.card F = 4)
    (hcenter : Subgroup.center SL(3,F) ≤ ρ.ker) :
    ∃ (ι : F →+* SplittingField ρ) (b c : Factor), PairSurvives b c ∧
      Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv (wordRep ι [b,c])) ∧
      schurDegree 2 ρ = (if b = c then 1 else 2) ∧
      Module.finrank (ZMod 2) V = (if b = c then 1 else 2) * wordDegree [b,c] := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Algebra (ZMod 2) (SplittingField ρ) := ZMod.algebra (SplittingField ρ) 2
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars (SplittingField ρ) ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep (SplittingField ρ)
  let ι : F →+* SplittingField ρ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := SplittingField ρ)).toRingHom
  have hc : Subgroup.center SL(3,F) ≤
      (extendScalars (SplittingField ρ) ρ.endFieldRep).ker := by
    intro g hg
    exact (scalarExtension_eq_one_iff ρ g).mpr (hcenter hg)
  obtain ⟨b,c,hbc,he⟩ := exists_pair_model ι hcard _ hc
  have hs := pair_schurDegree ρ hcard ι b c he
  refine ⟨ι,b,c,hbc,he,hs,?_⟩
  obtain ⟨e⟩ := he
  rw [finrank_eq_schurDegree_mul 2 ρ (SplittingField ρ), e.toLinearEquiv.finrank_eq,
    finrank_wordSpace, hs]

/-- The five nontrivial surviving pairs, without merging natural and dual models. -/
def NontrivialPair (b c : Factor) : Prop :=
  (b = .natural ∧ c = .natural) ∨ (b = .dual ∧ c = .dual) ∨
  (b = .trivial ∧ c = .adjoint) ∨ (b = .adjoint ∧ c = .trivial) ∨
  (b = .adjoint ∧ c = .adjoint)

theorem exists_nontrivial_binary_pair_model (hcard : Nat.card F = 4)
    (hcenter : Subgroup.center SL(3,F) ≤ ρ.ker) (hact : ∃ g, ρ g ≠ 1) :
    ∃ (ι : F →+* SplittingField ρ) (b c : Factor), NontrivialPair b c ∧
      Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv (wordRep ι [b,c])) ∧
      schurDegree 2 ρ = (if b = c then 1 else 2) ∧
      Module.finrank (ZMod 2) V = (if b = c then 1 else 2) * wordDegree [b,c] := by
  obtain ⟨ι,b,c,hbc,⟨e⟩,hs,hd⟩ := exists_binary_pair_model ρ hcard hcenter
  have hnt : ¬ (b = .trivial ∧ c = .trivial) := by
    rintro ⟨rfl,rfl⟩
    obtain ⟨g,hg⟩ := hact
    apply hg
    apply (scalarExtension_eq_one_iff ρ g).mp
    apply LinearMap.ext
    intro v
    apply e.toLinearEquiv.injective
    have he := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
    have hw : wordRep ι [.trivial,.trivial] g = 1 :=
      wordRep_eq_one_of_counts_zero ι _ (by decide) (by decide) g
    rw [hw] at he
    convert he using 1 <;> rfl
  have hh : NontrivialPair b c := by
    cases b <;> cases c <;> simp_all [PairSurvives, NontrivialPair]
  exact ⟨ι,b,c,hh,⟨e⟩,hs,hd⟩

/-- In particular the only nontrivial binary degrees are 9, 16 and 64. -/
theorem binary_dimension_cases (hcard : Nat.card F = 4)
    (hcenter : Subgroup.center SL(3,F) ≤ ρ.ker) (hact : ∃ g, ρ g ≠ 1) :
    Module.finrank (ZMod 2) V = 9 ∨ Module.finrank (ZMod 2) V = 16 ∨
      Module.finrank (ZMod 2) V = 64 := by
  obtain ⟨ι,b,c,hbc,_,_,hd⟩ := exists_nontrivial_binary_pair_model ρ hcard hcenter hact
  rcases hbc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    norm_num [wordDegree, Factor.dimension, show Factor.trivial ≠ Factor.adjoint by decide,
      show Factor.adjoint ≠ Factor.trivial by decide] at hd <;> simp [hd]

end CFSG.Quasithin.ChapterH.Section01To04.L3Four
