module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.BaumannApplication.Action
public import Theory.GroupTheory.PushingUp.BaumannBinary.NaturalAll

/-!
# The natural central quotient of the original adjacent-core closure

For X = ⟨Qδ^{Gλ}⟩ and P = Qδ inside X, the Baumann natural quotient now
includes field degree one. Its kernel is exactly V ∩ Z(X), and its
coordinates use the same supplied X/O₂(X) marking. The original embedding
of Qδ into the ambient completion is retained.

Source: DGS85, *Groups and Graphs*, (6.3–6.5), printed pp.120–122. The
(6.4) Sylow, characteristic-subgroup, self-centralization and marked-quotient
premises remain explicit for the graph-obstruction owner to discharge.
The separate full commutator bound and graph contradiction are not asserted.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
variable {G : Type*} [Group G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The original DGS (6.5) normal closure, at every positive binary degree. -/
theorem natural_projection_all (A B : Subgroup G) [Finite B]
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
    let V := BaumannBinary.centerClosure (coreInClosure A B)
    ∃ f : Additive V →ₗ[ZMod 2] (Fin 2 → F), Function.Surjective f ∧
      LinearMap.ker f = NormalElementaryQuotient.subspace V
        ((V ⊓ center (coreClosure A B)).subgroupOf V) ∧
      ∀ g v, f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        Matrix.mulVec (q g).val (f v) :=
  ⟨coreInClosure_image A B hAB,
    BaumannBinary.centerClosure_natural_projection_all (coreSylow A B hindex) hc hno
      q hq hk hn hF⟩
end CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
