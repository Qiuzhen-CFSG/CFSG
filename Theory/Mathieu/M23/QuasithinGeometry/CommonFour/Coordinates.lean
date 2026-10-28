module

public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Representation.MathieuCodeRestriction
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion.Certificate

/-!
# Native coordinate witnesses for the marked M23 cores

Three explicit permutations give a common geometric marking and the two
local conjugators used to bound intrinsic two-cores. Each is extended to
24 points fixing the distinguished point; images of the twelve Golay rows
certify membership in native M24. The proved point-stabilizer range then
certifies membership in native M23, retaining the literal point action.

The discovery script uses GAP only to suggest witnesses. The Lean kernel
checks all permutation, row and coordinate identities. Source: Aschbacher–Smith,
H.14.2(1) and the marking preceding H.14.1, printed pp.396–397.
-/

@[expose] public section
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.CommonFour
open M24LocalGeometry MathieuCode
set_option maxRecDepth 100000
set_option Elab.async false

def transportPerm : Equiv.Perm (Fin 23) where
  toFun := ![1, 21, 11, 12, 9, 22, 3, 15, 14, 13, 4, 10, 2, 19, 7, 5, 18, 0, 16, 17, 8, 6, 20]
  invFun := ![17, 0, 12, 6, 10, 15, 21, 14, 20, 4, 11, 2, 3, 9, 8, 7, 18, 19, 16, 13, 22, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def transportExtension : Equiv.Perm (Fin 24) where
  toFun := ![0, 21, 11, 12, 9, 22, 3, 15, 14, 13, 4, 10, 2, 19, 7, 5, 18, 23, 16, 17, 8, 6, 20, 1]
  invFun := ![0, 23, 12, 6, 10, 15, 21, 14, 20, 4, 11, 2, 3, 9, 8, 7, 18, 19, 16, 13, 22, 1, 5, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def transportRow : Fin 12 → Fin 4096 := ![487, 114, 1174, 272, 692, 194, 334, 310, 434, 2516, 100, 480]

private theorem transport_rows : ∀ i,
    m24PermuteMask transportExtension (m24GolayRow i) = m24GolayCode (transportRow i) := by
  decide +kernel

private theorem transport_extends : ∀ x,
    transportExtension (m23PointEmbedding x) = m23PointEmbedding (transportPerm x) := by
  decide +kernel

def quintetMovePerm : Equiv.Perm (Fin 23) where
  toFun := ![4, 1, 2, 3, 0, 16, 12, 19, 8, 15, 11, 10, 6, 13, 20, 9, 5, 22, 18, 7, 14, 21, 17]
  invFun := ![4, 1, 2, 3, 0, 16, 12, 19, 8, 15, 11, 10, 6, 13, 20, 9, 5, 22, 18, 7, 14, 21, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quintetMoveExtension : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 23, 16, 12, 19, 8, 15, 11, 10, 6, 13, 20, 9, 5, 22, 18, 7, 14, 21, 17, 4]
  invFun := ![0, 1, 2, 3, 23, 16, 12, 19, 8, 15, 11, 10, 6, 13, 20, 9, 5, 22, 18, 7, 14, 21, 17, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quintetMoveRow : Fin 12 → Fin 4096 := ![593, 1682, 1108, 1192, 1760, 176, 208, 1648, 1936, 1120, 608, 2720]

private theorem quintetMove_rows : ∀ i,
    m24PermuteMask quintetMoveExtension (m24GolayRow i) = m24GolayCode (quintetMoveRow i) := by
  decide +kernel

private theorem quintetMove_extends : ∀ x,
    quintetMoveExtension (m23PointEmbedding x) = m23PointEmbedding (quintetMovePerm x) := by
  decide +kernel

def heptadMovePerm : Equiv.Perm (Fin 23) where
  toFun := ![0, 1, 2, 10, 4, 6, 5, 8, 7, 9, 3, 13, 14, 11, 12, 15, 22, 20, 19, 18, 17, 21, 16]
  invFun := ![0, 1, 2, 10, 4, 6, 5, 8, 7, 9, 3, 13, 14, 11, 12, 15, 22, 20, 19, 18, 17, 21, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def heptadMoveExtension : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 10, 4, 6, 5, 8, 7, 9, 3, 13, 14, 11, 12, 15, 22, 20, 19, 18, 17, 21, 16, 23]
  invFun := ![0, 1, 2, 10, 4, 6, 5, 8, 7, 9, 3, 13, 14, 11, 12, 15, 22, 20, 19, 18, 17, 21, 16, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def heptadMoveRow : Fin 12 → Fin 4096 := ![1, 10, 12, 8, 24, 64, 32, 264, 136, 520, 2048, 1024]

private theorem heptadMove_rows : ∀ i,
    m24PermuteMask heptadMoveExtension (m24GolayRow i) = m24GolayCode (heptadMoveRow i) := by
  decide +kernel

private theorem heptadMove_extends : ∀ x,
    heptadMoveExtension (m23PointEmbedding x) = m23PointEmbedding (heptadMovePerm x) := by
  decide +kernel

private theorem native_of_extension (p : Equiv.Perm (Fin 23)) (e : Equiv.Perm (Fin 24))
    (he : e ∈ M24) (h0 : e 0 = 0)
    (hx : ∀ x, e (m23PointEmbedding x) = m23PointEmbedding (p x)) : p ∈ M23 := by
  have hr : (⟨e,he⟩ : M24) ∈ pointEmbedding.range := by
    rw [pointEmbedding_range]
    exact h0
  obtain ⟨g,hg⟩ := hr
  have hp : g.val = p := by
    apply Equiv.ext
    intro x
    apply m23PointEmbedding.injective
    rw [← pointEmbedding_apply, hg]
    exact hx x
  exact hp ▸ g.property

noncomputable def transport : M23 := ⟨transportPerm, by
  apply native_of_extension transportPerm transportExtension
  · apply M24LocalGeometry.PairOvergroups.QuotientConstruction.AffineLiftConstruction.mem_M24_of_rows
    intro i
    exact ⟨transportRow i, transport_rows i⟩
  · rfl
  · exact transport_extends⟩

theorem transport_embedding : (pointEmbedding transport).val = transportExtension := by
  apply Equiv.ext
  intro x
  by_cases h : x = 0
  · subst x
    exact pointEmbedding_fixed _
  · obtain ⟨i,hi⟩ := m23PointEquiv.surjective ⟨x,h⟩
    have he : m23PointEmbedding i = x := congrArg Subtype.val hi
    rw [← he, pointEmbedding_apply, transport_extends]
    rfl

noncomputable def quintetMove : M23 := ⟨quintetMovePerm, by
  apply native_of_extension quintetMovePerm quintetMoveExtension
  · apply M24LocalGeometry.PairOvergroups.QuotientConstruction.AffineLiftConstruction.mem_M24_of_rows
    intro i
    exact ⟨quintetMoveRow i, quintetMove_rows i⟩
  · rfl
  · exact quintetMove_extends⟩

theorem quintetMove_embedding : (pointEmbedding quintetMove).val = quintetMoveExtension := by
  apply Equiv.ext
  intro x
  by_cases h : x = 0
  · subst x
    exact pointEmbedding_fixed _
  · obtain ⟨i,hi⟩ := m23PointEquiv.surjective ⟨x,h⟩
    have he : m23PointEmbedding i = x := congrArg Subtype.val hi
    rw [← he, pointEmbedding_apply, quintetMove_extends]
    rfl

noncomputable def heptadMove : M23 := ⟨heptadMovePerm, by
  apply native_of_extension heptadMovePerm heptadMoveExtension
  · apply M24LocalGeometry.PairOvergroups.QuotientConstruction.AffineLiftConstruction.mem_M24_of_rows
    intro i
    exact ⟨heptadMoveRow i, heptadMove_rows i⟩
  · rfl
  · exact heptadMove_extends⟩

theorem heptadMove_embedding : (pointEmbedding heptadMove).val = heptadMoveExtension := by
  apply Equiv.ext
  intro x
  by_cases h : x = 0
  · subst x
    exact pointEmbedding_fixed _
  · obtain ⟨i,hi⟩ := m23PointEquiv.surjective ⟨x,h⟩
    have he : m23PointEmbedding i = x := congrArg Subtype.val hi
    rw [← he, pointEmbedding_apply, heptadMove_extends]
    rfl

/-- Extend a native point table by the fixed distinguished point. -/
def extendPoint (p : Fin 23 → Fin 23) (x : Fin 24) : Fin 24 :=
  if x = 0 then 0 else m23PointEmbedding (p ⟨x.val % 23, Nat.mod_lt _ (by decide)⟩)

private theorem embedding_back : ∀ x : Fin 24, x ≠ 0 →
    m23PointEmbedding ⟨x.val % 23, Nat.mod_lt _ (by decide)⟩ = x := by decide +kernel

theorem pointEmbedding_apply_all (g : M23) (x : Fin 24) :
    (pointEmbedding g).val x = extendPoint g.val x := by
  by_cases h : x = 0
  · subst x
    exact pointEmbedding_fixed g
  · rw [extendPoint, if_neg h, ← pointEmbedding_apply, embedding_back x h]

end Sporadic.Mathieu.M23Geometry.CommonFour
