module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.BaumannApplication.SourceNatural
public import Theory.GroupTheory.PushingUp.BaumannBinary.CommutatorAll

/-!
# Both Baumann clauses on the actual adjacent-core closure

For X = ⟨Qδ^{Gλ}⟩ and qλ = 2ⁿ with n≥1, the explicitly retained (6.4)
premises give [O₂(X),X] ≤ V and the exact natural action on V/(V ∩ Z(X)).
The full X is the commutator actor. The natural quotient keeps the original
marking and every p.113 consequence. The original Qδ inclusion is retained.
Construction of the (6.4) premises and the graph contradiction remain with
the setup/obstruction owner. Both Baumann clauses are proved here at every
positive binary degree.

Source: DGS85, *Groups and Graphs*, (6.3–6.5), printed pp.120–122,
and the natural-module definition and consequences, pp.112–113.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
variable {G : Type*} [Group G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Both source clauses of (6.3), with the independent (6.4) inputs explicit. -/
theorem source_conclusions_large (A B : Subgroup G) [Finite B]
    (hAB : (pCore 2 A).map A.subtype ≤ B)
    (hindex : ¬ 2 ∣ (coreInClosure A B).index)
    (hc : centralizer (pCore 2 (coreClosure A B) : Set (coreClosure A B)) ≤
      pCore 2 (coreClosure A B))
    (hno : NoCharacteristicNormal (coreInClosure A B))
    (q : coreClosure A B →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (coreClosure A B))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    (coreInClosure A B).map (originalEmbedding A B) = (pCore 2 A).map A.subtype ∧
    ⁅pCore 2 (coreClosure A B),(⊤ : Subgroup (coreClosure A B))⁆ ≤
      BaumannBinary.centerClosure (coreInClosure A B) ∧
    letI : IsElementaryAbelian 2 (BaumannBinary.centerClosure (coreInClosure A B)) :=
      (BaumannBinary.centerClosure_reduced (coreSylow A B hindex) hc).elementary
    let hker := hk.trans (action_kernel A B hindex hc hno q hq hk (by omega) hF).symm
    let ρ := NormalElementaryQuotient.representation
      (BaumannBinary.centerClosure (coreInClosure A B)) q hq hker
    let σ := SL2SylowFixedRecognition.centralQuotient ρ
    let S := (coreSylow A B hindex).mapSurjective hq
    IsSourceNatural σ S n ∧ σ.IsIrreducible ∧
      Nat.card (fixedSpace σ S) = 2^n ∧
      (∀ t ∈ (S : Subgroup SL(2,F)), t ≠ 1 →
        fixedSpace σ (zpowers t) = fixedSpace σ S) ∧
      (∀ g ∉ normalizer (S : Set SL(2,F)),
        IsCompl (fixedSpace σ S) (fixedSpace σ (g • S : Sylow 2 SL(2,F)))) ∧
      (∀ v w, v ≠ 0 → w ≠ 0 → ∃ g, σ g v = w) :=
  ⟨coreInClosure_image A B hAB,
    BaumannBinary.core_commutator_le_centerClosure (coreSylow A B hindex) hc hno q hq hk hn hF,
    BaumannBinary.centerClosure_source_natural (coreSylow A B hindex) hc hno q hq hk (by omega) hF⟩

/-- DGS85 (6.3) on the literal adjacent-core closure at every positive binary
degree. The independent (6.4) premises remain with the graph obstruction owner. -/
theorem source_conclusions (A B : Subgroup G) [Finite B]
    (hAB : (pCore 2 A).map A.subtype ≤ B)
    (hindex : ¬ 2 ∣ (coreInClosure A B).index)
    (hc : centralizer (pCore 2 (coreClosure A B) : Set (coreClosure A B)) ≤
      pCore 2 (coreClosure A B))
    (hno : NoCharacteristicNormal (coreInClosure A B))
    (q : coreClosure A B →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (coreClosure A B))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    (coreInClosure A B).map (originalEmbedding A B) = (pCore 2 A).map A.subtype ∧
    ⁅pCore 2 (coreClosure A B),(⊤ : Subgroup (coreClosure A B))⁆ ≤
      BaumannBinary.centerClosure (coreInClosure A B) ∧
    letI : IsElementaryAbelian 2 (BaumannBinary.centerClosure (coreInClosure A B)) :=
      (BaumannBinary.centerClosure_reduced (coreSylow A B hindex) hc).elementary
    let hker := hk.trans (action_kernel A B hindex hc hno q hq hk hn hF).symm
    let ρ := NormalElementaryQuotient.representation
      (BaumannBinary.centerClosure (coreInClosure A B)) q hq hker
    let σ := SL2SylowFixedRecognition.centralQuotient ρ
    let S := (coreSylow A B hindex).mapSurjective hq
    IsSourceNatural σ S n ∧ σ.IsIrreducible ∧
      Nat.card (fixedSpace σ S) = 2^n ∧
      (∀ t ∈ (S : Subgroup SL(2,F)), t ≠ 1 →
        fixedSpace σ (zpowers t) = fixedSpace σ S) ∧
      (∀ g ∉ normalizer (S : Set SL(2,F)),
        IsCompl (fixedSpace σ S) (fixedSpace σ (g • S : Sylow 2 SL(2,F)))) ∧
      (∀ v w, v ≠ 0 → w ≠ 0 → ∃ g, σ g v = w) :=
  ⟨coreInClosure_image A B hAB,
    BaumannBinary.core_commutator_le_centerClosure_all (coreSylow A B hindex) hc hno q hq hk hn hF,
    BaumannBinary.centerClosure_source_natural (coreSylow A B hindex) hc hno q hq hk hn hF⟩
end CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
