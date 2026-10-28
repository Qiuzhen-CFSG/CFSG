module

public import Theory.Mathieu.M22.CentralCoverPrelude
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates
public import Theory.Representation.BinaryPermutationSixCover.Facts
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.GroupTheory.PerfectCentralSupplement
public import Theory.GroupTheory.Commutator.PerfectQuotient

/-!
# Perfect hexad preimages in central two-covers of M₂₂

The native hexad stabilizer is perfect: its A₆ section is perfect, and the
augmentation module generates its natural translation quotient by commutators.
For a perfect ambient central two-cover, transfer at the hexad index 77 puts
the entire central kernel in the local commutator subgroup. The perfect native
quotient then makes the full hexad preimage perfect.

Source: Aschbacher–Smith I.2.2(6), printed p.412. All maps use the original
central quotient and the chosen actual hexad.
-/

public section
noncomputable section
open Subgroup Representation
open scoped Pointwise
namespace Sporadic.Mathieu

/-- Every actual hexad stabilizer is perfect in the native degree-22 model. -/
theorem m22HexadStabilizer_isPerfect {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Group.IsPerfect (MulAction.stabilizer M22 B) := by
  let H := MulAction.stabilizer M22 B
  let N := (m22SetAction B).ker
  let s := m22HexadSection hB
  let e := m22HexadNaturalCoordinates hB
  let p : Multiplicative (BinaryPermutation.core (Fin 6)) →* N :=
    e.symm.toMonoidHom.comp (BinaryPermutation.coreToNatural (Fin 6)).toAddMonoidHom.toMultiplicative
  let j : Multiplicative (BinaryPermutation.core (Fin 6)) →* H := N.subtype.comp p
  have hp : Function.Surjective p :=
    e.symm.surjective.comp (BinaryPermutation.coreToNatural_surjective (Ω := Fin 6))
  have hjact (a : alternatingGroup (Fin 6)) (v : BinaryPermutation.core (Fin 6)) :
      j (Multiplicative.ofAdd (BinaryPermutation.alternatingCoreRepresentation (Fin 6) a v)) =
        s a * j (Multiplicative.ofAdd v) * (s a)⁻¹ := by
    have he : p (Multiplicative.ofAdd
        (BinaryPermutation.alternatingCoreRepresentation (Fin 6) a v)) =
        MulAut.conjNormal (s a) (p (Multiplicative.ofAdd v)) := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [m22HexadNaturalCoordinates_section hB]
      simp only [p, e, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
      exact BinaryPermutation.coreToNatural_equivariant a.val v
    exact congrArg Subtype.val he
  let C := (commutator H).comap j
  let W : Submodule (ZMod 2) (BinaryPermutation.core (Fin 6)) :=
    AddSubgroup.toZModSubmodule 2 C.toAddSubgroup
  have hW : Coinvariants.ker (BinaryPermutation.alternatingCoreRepresentation (Fin 6)) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    change j (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 6) a v - v)) ∈ commutator H
    change j (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 6) a v) /
        Multiplicative.ofAdd v) ∈ commutator H
    rw [map_div, hjact, div_eq_mul_inv]
    exact Subgroup.commutator_mem_commutator (mem_top (s a)) (mem_top (j (Multiplicative.ofAdd v)))
  rw [BinaryPermutation.alternatingSix_core_generated] at hW
  have hN : N ≤ commutator H := by
    intro x hx
    obtain ⟨v, hv⟩ := hp ⟨x, hx⟩
    have hm : j v ∈ commutator H := hW (Submodule.mem_top : v.toAdd ∈ (⊤ : Submodule (ZMod 2) _))
    change (p v).val ∈ commutator H at hm
    rwa [hv] at hm
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hs : s.range ≤ commutator H := by
    let : Group.IsPerfect s.range := Group.IsPerfect.range s
    rw [← Subgroup.commutator_eq_self (H := s.range)]
    exact commutator_mono le_top le_top
  exact ⟨top_unique ((m22HexadSection_isComplement hB).sup_eq_top ▸ sup_le hN hs)⟩

namespace M22CentralCover

/-- The original full hexad preimage is perfect whenever the ambient cover is
perfect and its actual center is a two-group. -/
theorem hexadPreimage_isPerfect {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* M22) (hZ : IsPGroup 2 (center K))
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Group.IsPerfect (preimage e (MulAction.stabilizer M22 B)) := by
  let H := MulAction.stabilizer M22 B
  let I := preimage e H
  let q := localProjection e H
  let : Group.IsPerfect H := m22HexadStabilizer_isPerfect hB
  have hi : I.index = 77 := by
    change (H.comap (projection e)).index = 77
    rw [H.index_comap_of_surjective (projection_surjective e)]
    have hc := H.card_mul_index
    rw [m22Hexad_stabilizer_card hB, m22_order] at hc
    omega
  have hz : center K ≤ ⁅I,I⁆ := central_pSubgroup_le_commutator I (center K)
    (center_le_preimage e H) le_rfl hZ (by rw [hi]; decide)
  have hk : q.ker ≤ commutator I := by
    rw [localProjection_ker]
    intro x hx
    have hm := hz hx
    rw [← map_subtype_commutator] at hm
    obtain ⟨y, hy, he⟩ := hm
    exact (Subtype.ext he : y = x) ▸ hy
  exact ⟨(sup_of_le_right hk).symm.trans
    (CentralExtension.ker_sup_commutator_eq_top_of_surjective q (localProjection_surjective e H))⟩

end M22CentralCover
end Sporadic.Mathieu
