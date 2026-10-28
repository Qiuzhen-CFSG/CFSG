module
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Binary rank-one sections in prime-field PSL₂

A perfect group with simple binary SL₂ two-core quotient has only two-group
solvable kernels. A homomorphism with solvable kernel into prime-field PSL₂
therefore preserves that two-core quotient. A proper nonsolvable image is
A₅ by Dickson's theorem. A full image has two-rank two, forcing the binary
field to have order four. Both cases give the original A₅ quotient.

Source application: Aschbacher–Smith A.3.6, A.3.12 and 10.2.3,
printed pp.43–48 and 745–746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2

/-- A solvable-kernel image in prime-field PSL₂ forces the original binary quotient to be A₅. -/
theorem binary_core_section_of_solvable_kernel
    {X F : Type*} [_root_.Group X] [Finite X] [Group.IsPerfect X]
    [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] (hp : 3 < p) (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n) (r : (X ⧸ pCore 2 X) ≃* SL(2,F))
    (f : X →* PSL(2,ZMod p)) [Group.IsSolvable f.ker] :
    Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) := by
  have hfour : 3 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hh
    omega
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup SL(2,F) := (sl2QuotientEquiv F).isSimpleGroup
  let : IsSimpleGroup (X ⧸ pCore 2 X) := r.isSimpleGroup
  let : Nontrivial X := (QuotientGroup.mk'_surjective (pCore 2 X)).nontrivial
  let R := f.range
  have hns : ¬ Group.IsSolvable R := by
    intro hs
    let := hs
    exact Group.IsPerfect.not_isSolvable X
      (Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by simp))
  have hmodels : Nonempty (R ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (R ≃* PSL(2,ZMod p)) := by
    by_cases ht : R = ⊤
    · exact Or.inr ⟨(MulEquiv.subgroupCongr ht).trans topEquiv⟩
    · exact Or.inl (prime_nonsolvable_proper_is_alternating_five
        ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (by simp) R ht hns).2.2
  let : IsSimpleGroup PSL(2,ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ p by omega))
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup R := by
    rcases hmodels with ha | ha
    · obtain ⟨a⟩ := ha
      exact a.isSimpleGroup
    · obtain ⟨a⟩ := ha
      exact a.isSimpleGroup
  let := hs
  have hc : pCore 2 R = ⊥ := by
    rcases (inferInstance : (pCore 2 R).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have ht' : IsPGroup 2 R := pCore_isPGroup.of_equiv
        ((MulEquiv.subgroupCongr ht).trans topEquiv)
      let := ht'.isNilpotent
      exact (hns inferInstance).elim
  let : Group.IsSolvable f.rangeRestrict.ker := by
    have hk : f.rangeRestrict.ker = f.ker := by ext x; simp
    rw [hk]
    infer_instance
  let b : (X ⧸ pCore 2 X) ≃* R :=
    (PerfectCoreTwoExtension.solvableKernelQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective).trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
  rcases hmodels with ha | ha
  · obtain ⟨a⟩ := ha
    exact ⟨b.trans a⟩
  · obtain ⟨a⟩ := ha
    let e : PSL(2,F) ≃* PSL(2,ZMod p) :=
      (sl2QuotientEquiv F).symm.trans (r.symm.trans (b.trans a))
    have hl := root_two_rank_ge F hF
    rw [primeRank_equiv 2 e,primeField_two_rank hp] at hl
    have hn2 : n = 2 := by omega
    have hf4 : Nat.card F = 4 := by rw [hF,hn2]; norm_num
    obtain ⟨a5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hf4
    exact ⟨r.trans ((sl2QuotientEquiv F).trans a5)⟩
end Theory.PSL2
