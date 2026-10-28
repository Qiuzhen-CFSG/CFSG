module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.BaumannApplication.NaturalAll
public import Theory.GroupTheory.PushingUp.BaumannBinary.SourceNatural

/-!
# Source naturality for the literal DGS (6.5) normal closure

For X = ⟨Qδ^{Gλ}⟩, the (6.4) hypotheses explicitly retained below give every
DGS p.112–113 natural-module property on the original quotient V/(V ∩ Z(X)).
The Sylow image is the image of the original Qδ under the same marked
X/O₂(X) map, including field degree one. The original ambient inclusion is
also retained. This supplies the natural-module half of (6.3) to the graph
obstruction; [O₂(X),X] ≤ V remains a separate obligation of its proof owner.

Source: DGS85, *Groups and Graphs*, printed pp.112–113,120–122.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
variable {G : Type*} [Group G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The natural clause of (6.3), applied to the exact group and Sylow of (6.5). -/
theorem source_natural (A B : Subgroup G) [Finite B]
    (hAB : (pCore 2 A).map A.subtype ≤ B)
    (hindex : ¬ 2 ∣ (coreInClosure A B).index)
    (hc : centralizer (pCore 2 (coreClosure A B) : Set (coreClosure A B)) ≤
      pCore 2 (coreClosure A B))
    (hno : NoCharacteristicNormal (coreInClosure A B))
    (q : coreClosure A B →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (coreClosure A B))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    (coreInClosure A B).map (originalEmbedding A B) = (pCore 2 A).map A.subtype ∧
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
    BaumannBinary.centerClosure_source_natural (coreSylow A B hindex) hc hno q hq hk hn hF⟩
end CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
