module

public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Basic
public import Theory.Mathieu.M23.Properties.Transitivity
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Geometry

/-!
# Comparing a point stabilizer inside the M₂₃ triple stabilizer with M₂₂

The native point-stabilizer equivalence extends M₂₂ permutations by fixing
point 9. Its relabelling sends the pair {1,2} to {18,7}. Equivariance on
augmented finite sets identifies the M₂₂ pair stabilizer with the subgroup
fixing 9 inside the M₂₃ stabilizer of {9,18,7}. Three-transitivity transports
{0,1,2} to this marked triple.

These are actual equivalences of permutation subgroups. No abstract extension
recognition or maximal-local coverage is used.

Source: GLS3, Table 5.3d, printed p.265; the local inspection in
Aschbacher--Smith, 15.3.41--42, printed p.1138. The point-stabilizer comparison
is constructed in `M23.Properties.Simplicity`.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.SylowTwoLocals.TripleSolvable
open M22ValueBound.Concrete

/-- The image of the M₂₂ pair, augmented by the fixed point 9. -/
noncomputable abbrev markedTriple := m22M23AugmentedBlock m22Pair12

/-- The setwise stabilizer of the marked triple {9,18,7}. -/
noncomputable abbrev markedStabilizer := MulAction.stabilizer M23 markedTriple

/-- Fixing point 9 inside the setwise triple stabilizer. -/
noncomputable abbrev markedPointStabilizer :=
  MulAction.stabilizer markedStabilizer (9 : Fin 23)

private theorem restrict_equiv (g : M22) :
    m23PointStabilizerNineRestrictHom (m23EquivM22PointStabilizer g) = g.val := by
  apply Equiv.Perm.viaEmbeddingHom_injective m22M23PointEmbedding
  exact m22M23RelabelHom_restrict (m23EquivM22PointStabilizer g)

/-- The actual point-stabilizer comparison intertwines the pair and triple actions. -/
theorem marked_smul (g : M22) :
    (m23EquivM22PointStabilizer g).val • markedTriple =
      m22M23AugmentedBlock (g • m22Pair12) := by
  change (m23EquivM22PointStabilizer g).val.val • markedTriple = _
  rw [m23PointStabilizerNine_smul_augmentedBlock, restrict_equiv]
  rfl

private theorem mem_first_iff (g : M22) :
    g ∈ first ↔ (m23EquivM22PointStabilizer g).val ∈ markedStabilizer := by
  change g • m22Pair12 = m22Pair12 ↔ _ • markedTriple = markedTriple
  rw [marked_smul]
  exact m22M23AugmentedBlock_injective.eq_iff.symm

private noncomputable def firstToMarkedPoint : first →* markedPointStabilizer where
  toFun g := ⟨⟨(m23EquivM22PointStabilizer g.val).val,
    (mem_first_iff g.val).mp g.property⟩,
    (m23EquivM22PointStabilizer g.val).property⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change (m23EquivM22PointStabilizer (1 : M22)).val = 1
    exact congrArg Subtype.val (map_one m23EquivM22PointStabilizer)
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    change (m23EquivM22PointStabilizer (g.val * h.val)).val = _
    exact congrArg Subtype.val (map_mul m23EquivM22PointStabilizer g.val h.val)

private theorem firstToMarkedPoint_bijective : Function.Bijective firstToMarkedPoint := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply m23EquivM22PointStabilizer.injective
    apply Subtype.ext
    exact congrArg (fun z : markedPointStabilizer => z.val.val) h
  · intro x
    obtain ⟨g, hg⟩ := m23EquivM22PointStabilizer.surjective ⟨x.val.val, x.property⟩
    have hm : g ∈ first := (mem_first_iff g).mpr (by rw [hg]; exact x.val.property)
    refine ⟨⟨g, hm⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (m23EquivM22PointStabilizer g).val = x.val.val
    exact congrArg Subtype.val hg

/-- The native M₂₂ pair stabilizer is the point-9 stabilizer inside the
marked M₂₃ triple stabilizer. -/
noncomputable def firstEquivMarkedPoint : first ≃* markedPointStabilizer :=
  MulEquiv.ofBijective firstToMarkedPoint firstToMarkedPoint_bijective

/-- Three-transitivity carries the specified triple to the marked triple. -/
theorem exists_triple_transport : ∃ g : M23,
    g • ({0, 1, 2} : Finset (Fin 23)) = markedTriple := by
  let : MulAction.IsMultiplyPretransitive M23 (Fin 23) 4 := m23_isFourPretransitive
  let : MulAction.IsMultiplyPretransitive M23 (Fin 23) 3 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 3 ≤ 4) (by simp)
  let a : Fin 3 ↪ Fin 23 := ⟨![0, 1, 2], by decide +kernel⟩
  let b : Fin 3 ↪ Fin 23 := ⟨![9, 18, 7], by decide +kernel⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M23 a b
  have h0 : g • (0 : Fin 23) = 9 := congrArg (fun f : Fin 3 ↪ Fin 23 => f 0) hg
  have h1 : g • (1 : Fin 23) = 18 := congrArg (fun f : Fin 3 ↪ Fin 23 => f 1) hg
  have h2 : g • (2 : Fin 23) = 7 := congrArg (fun f : Fin 3 ↪ Fin 23 => f 2) hg
  refine ⟨g, ?_⟩
  have hm : markedTriple = ({9, 18, 7} : Finset (Fin 23)) := by decide +kernel
  rw [hm, Finset.smul_finset_insert, Finset.smul_finset_insert,
    Finset.smul_finset_singleton, h0, h1, h2]

end Sporadic.Mathieu.M23Geometry.SylowTwoLocals.TripleSolvable
