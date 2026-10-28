module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction
public import Theory.Representation.ZeroHecke.TypeA4Eigenvector

/-!
# Existence of binary SL₄ local highest vectors

Adjoin a zero fourth operator to the type-A₃ action on upper-fixed vectors.
This satisfies the already checked type-A₄ zero-Hecke relations, so its
finite word argument gives a common nonzero zero-or-one eigenvector. The
rank-one identities convert it into the explicit local highest-vector data.
No irreducibility, splitting-field or absolute-irreducibility premise is needed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.3(11)--(12), printed pp.354,356--357. The elementary root proofs adapt
the binary SL₅ highest-vector development in this repository to rank three.
-/

@[expose] public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

open HeckeAction

/-- Every nonzero finite-dimensional binary SL₄ module contains a nonzero
upper-fixed vector satisfying all three rank-one alternatives. -/
theorem exists_localHighestVector
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) Group V) :
    ∃ (J : Finset (Fin 3)) (v : V), v ≠ 0 ∧ LocalHighestVector ρ J v := by
  classical
  let : Nontrivial (upperFixedSubmodule ρ) := upperFixedSubmodule_nontrivial ρ
  -- Adjoining a zero fourth operator realizes the type-A₃ relations inside
  -- the already checked type-A₄ finite word calculation.
  let T : Fin 4 → Module.End (ZMod 2) (upperFixedSubmodule ρ) :=
    ![restrictedOperator ρ 0, restrictedOperator ρ 1, restrictedOperator ρ 2, 0]
  have hidem : ∀ i, T i * T i = T i := by
    intro i
    fin_cases i <;> simp [T, restrictedOperator_sq]
  have hc02 := (restrictedOperator_commute ρ 0 2 (Or.inl (by decide))).eq
  have hcomm : ∀ i j, i.val + 1 < j.val → T i * T j = T j * T i := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [T]
  have hb01 := restrictedOperator_braid ρ 0 1 (by decide)
  have hb12 := restrictedOperator_braid ρ 1 2 (by decide)
  have hbraid : ∀ i j, i.val + 1 = j.val → T i * T j * T i = T j * T i * T j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [T]
  obtain ⟨v, hv, heigen⟩ := ZeroHecke.exists_common_zero_or_fixed T ⟨hidem, hcomm, hbraid⟩
  have heigen' (i : Fin 3) : restrictedOperator ρ i v = v ∨ restrictedOperator ρ i v = 0 := by
    have he := heigen i.castSucc
    fin_cases i <;> simpa [T] using he
  let J : Finset (Fin 3) := Finset.univ.filter (fun i => restrictedOperator ρ i v = v)
  refine ⟨J, (v : V), fun h => hv (Subtype.ext h), v.property, ?_, ?_⟩
  · intro i hi
    have hnot : restrictedOperator ρ i v ≠ v := by simpa [J] using hi
    exact (restrictedOperator_eq_zero_iff ρ i v).mp ((heigen' i).resolve_left hnot)
  · intro i hi
    exact (restrictedOperator_eq_self_iff ρ i v).mp ((Finset.mem_filter.mp hi).2)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
