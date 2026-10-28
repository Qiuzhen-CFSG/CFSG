module
public import Theory.GroupTheory.PushingUp.BaumannBinary.NaturalQuotient

/-!
# The original adjacent-core closure in DGS85 (6.5)

For the two original stabilizers A = Gδ and B = Gλ, X is the normal
closure in B of the embedded O₂(A). The explicit inclusion hypothesis
ensures that restriction to B loses no part of that original core. Only B
needs to be finite; the ambient completion may be infinite.

The odd-index input is exactly the Sylow assertion of (6.4)(a), the
characteristic obstruction is (6.4)(b), and the marked quotient is (6.4)(c).
Self-centralization of O₂(X) is retained explicitly. These premises give
the action-kernel reduction at every binary degree, and, for n > 1, the
natural projection on the original V with kernel precisely V ∩ Z(X).
They do not assert the separate commutator bound or the graph contradiction.
Their construction and final discharge remain with the DGS (6.4–6.5) owner.

Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs* (1985),
(6.3–6.5), printed pp.120–122.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
variable {G : Type*} [Group G]

/-- X = ⟨Qδ^{Gλ}⟩, formed inside the original opposite stabilizer. -/
@[expose] def coreClosure (A B : Subgroup G) : Subgroup B :=
  normalClosure (((pCore 2 A).map A.subtype).subgroupOf B : Set B)

/-- The original Qδ as an intrinsic subgroup of X. -/
@[expose] def coreInClosure (A B : Subgroup G) : Subgroup (coreClosure A B) :=
  (((pCore 2 A).map A.subtype).subgroupOf B).subgroupOf (coreClosure A B)

/-- The inclusion X → Gλ → G; no quotient is inserted. -/
@[expose] def originalEmbedding (A B : Subgroup G) : coreClosure A B →* G :=
  B.subtype.comp (coreClosure A B).subtype

theorem coreInClosure_isPGroup (A B : Subgroup G) :
    IsPGroup 2 (coreInClosure A B) :=
  ((pCore_isPGroup (p := 2) (G := A)).map A.subtype).comap_subtype.comap_subtype

theorem coreInClosure_image (A B : Subgroup G)
    (hAB : (pCore 2 A).map A.subtype ≤ B) :
    (coreInClosure A B).map (originalEmbedding A B) = (pCore 2 A).map A.subtype := by
  change ((coreInClosure A B).map (B.subtype.comp (coreClosure A B).subtype)) = _
  rw [←map_map]
  change (((((pCore 2 A).map A.subtype).subgroupOf B).subgroupOf
    (coreClosure A B)).map (coreClosure A B).subtype).map B.subtype = _
  rw [map_subgroupOf_eq_of_le (show ((pCore 2 A).map A.subtype).subgroupOf B ≤
    coreClosure A B from le_normalClosure), map_subgroupOf_eq_of_le hAB]

@[expose] noncomputable def coreSylow (A B : Subgroup G)
    (hindex : ¬ 2 ∣ (coreInClosure A B).index) : Sylow 2 (coreClosure A B) :=
  (coreInClosure_isPGroup A B).toSylow hindex

theorem coreSylow_image (A B : Subgroup G)
    (hAB : (pCore 2 A).map A.subtype ≤ B)
    (hindex : ¬ 2 ∣ (coreInClosure A B).index) :
    ((coreSylow A B hindex : Sylow 2 (coreClosure A B)) : Subgroup (coreClosure A B)).map
      (originalEmbedding A B) = (pCore 2 A).map A.subtype :=
  coreInClosure_image A B hAB

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

theorem action_kernel (A B : Subgroup G) [Finite B]
    (hindex : ¬ 2 ∣ (coreInClosure A B).index)
    (hc : centralizer (pCore 2 (coreClosure A B) : Set (coreClosure A B)) ≤
      pCore 2 (coreClosure A B))
    (hno : NoCharacteristicNormal (coreInClosure A B))
    (q : coreClosure A B →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (coreClosure A B))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    centralizer (BaumannBinary.centerClosure (coreInClosure A B) : Set (coreClosure A B)) =
      pCore 2 (coreClosure A B) :=
  BaumannBinary.centerClosure_centralizer (coreSylow A B hindex) hc hno q hq hk hn hF

theorem natural_projection (A B : Subgroup G) [Finite B]
    (hAB : (pCore 2 A).map A.subtype ≤ B)
    (hindex : ¬ 2 ∣ (coreInClosure A B).index)
    (hc : centralizer (pCore 2 (coreClosure A B) : Set (coreClosure A B)) ≤
      pCore 2 (coreClosure A B))
    (hno : NoCharacteristicNormal (coreInClosure A B))
    (q : coreClosure A B →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (coreClosure A B))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
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
    BaumannBinary.centerClosure_natural_projection (coreSylow A B hindex) hc hno
      q hq hk hn hF⟩
end CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
