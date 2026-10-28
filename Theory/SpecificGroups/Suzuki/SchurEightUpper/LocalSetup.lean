module

public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.SpecificGroups.Suzuki.SchurEightUpper.Pairing

/-!
# The third commutator in the Sz(8) universal cover

Let `P` be the full preimage of the standard root subgroup under the literal
universal projection, and set `D = [P,P]` and `J = [P,D]`. The source root
group has derived subgroup equal to its center. Thus `J` lies in the covering
kernel and is central. The three-subgroups lemma makes `D` abelian, while
transfer puts the whole covering kernel in `D`.

The shared `PairingData` interface specifies an additive mixed commutator
pairing generating this actual `J`, with its torus and Jacobi identities.
Constructing the pairing and proving the reverse containment `Kernel 1 ≤ J`
are independent inputs to the final upper-bound assembly.

Sources: Huppert--Blackburn III, XI.3.1--3.3 for the root group; the central
transfer reduction in `SchurCoverReduction`; Aschbacher--Smith I.1.3(5),
printed p.407/PDF p.418, and GLS3 §6.1 for the intended multiplier bound.
-/

@[expose] public noncomputable section
open Subgroup

namespace BenderSuzuki.MatrixGroups.SchurCover.EightLocal

local instance : Fact (0 < (1 : ℕ)) := ⟨by decide⟩

/-- The literal coordinate field of `SuzukiMatrixGroup 1`. -/
abbrev Field := PFAppendixIII.BinaryGaloisField 3
/-- The original universal projection, with no quotient identification. -/
abbrev projection := PerfectCentralCovering.universalProjection (SuzukiMatrixGroup 1)
/-- The full preimage of the standard root subgroup. -/
abbrev RootPreimage : Subgroup (CoverGroup 1) := (SuzukiRootSubgroup 1).comap projection
/-- The third term `[P,[P,P]]` in the covering root preimage. -/
abbrev ThirdCommutator : Subgroup (CoverGroup 1) := ⁅RootPreimage, ⁅RootPreimage, RootPreimage⁆⁆

/-- The standard root group is special, by the source coordinate theorem. -/
theorem root_derived_eq_center :
    commutator (SuzukiRootSubgroup 1) = center (SuzukiRootSubgroup 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ :=
    External.huppert_blackburn_XI_3_1 1 (by decide) (suzukiTits 1) (suzukiTits_sq 1)
  change commutator (SuzukiRootClosure 1) = center (SuzukiRootClosure 1) at hc
  let e : SuzukiRootSubgroup 1 ≃* SuzukiRootClosure 1 :=
    subgroupOfEquivOfLe (suzukiRootClosure_le 1)
  have he : (commutator (SuzukiRootSubgroup 1)).map e.toMonoidHom =
      center (SuzukiRootClosure 1) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    exact hc
  ext x
  constructor
  · intro hx
    have hz : e x ∈ center (SuzukiRootClosure 1) := he ▸ mem_map_of_mem e.toMonoidHom hx
    exact ((centerCongr e).symm ⟨e x, hz⟩).property
  · intro hx
    have hz : e x ∈ center (SuzukiRootClosure 1) := (centerCongr e ⟨x, hx⟩).property
    rw [← he] at hz
    obtain ⟨y, hy, hyx⟩ := hz
    exact e.injective hyx ▸ hy

/-- The base root group has nilpotency class at most two. -/
theorem root_third_eq_bot :
    ⁅SuzukiRootSubgroup 1, ⁅SuzukiRootSubgroup 1, SuzukiRootSubgroup 1⁆⁆ = ⊥ := by
  let T := SuzukiRootSubgroup 1
  have ht : ⁅(⊤ : Subgroup T), commutator T⁆ = ⊥ := by
    rw [root_derived_eq_center]
    exact commutator_center_right _
  have hmap := congrArg (Subgroup.map T.subtype) ht
  rw [map_commutator, ← MonoidHom.range_eq_map, T.range_subtype, map_subtype_commutator, Subgroup.map_bot] at hmap
  exact hmap

theorem rootPreimage_map : RootPreimage.map projection = SuzukiRootSubgroup 1 := by
  exact map_comap_eq_self_of_surjective
    (PerfectCentralCovering.universalCover (SuzukiMatrixGroup 1)).surjective _

/-- Projecting a third commutator kills it in the base root group. -/
theorem third_le_kernel : ThirdCommutator ≤ Kernel 1 := by
  change ThirdCommutator ≤ projection.ker
  rw [← MonoidHom.comap_bot]
  apply map_le_iff_le_comap.mp
  rw [map_commutator, map_commutator, rootPreimage_map, root_third_eq_bot]

theorem third_le_center : ThirdCommutator ≤ center (CoverGroup 1) :=
  third_le_kernel.trans (PerfectCentralCovering.universalCover (SuzukiMatrixGroup 1)).ker_le_center

abbrev DerivedPreimage : Subgroup (CoverGroup 1) := ⁅RootPreimage, RootPreimage⁆

/-- Transfer places the entire kernel in the local derived subgroup. -/
theorem kernel_le_derived : Kernel 1 ≤ DerivedPreimage :=
  kernel_le_rootPreimage_commutator (by decide)
    (PerfectCentralCovering.universalCover (SuzukiMatrixGroup 1))

theorem derived_map : DerivedPreimage.map projection =
    ⁅SuzukiRootSubgroup 1, SuzukiRootSubgroup 1⁆ := by
  rw [map_commutator, rootPreimage_map]

/-- Central third commutators make the local derived subgroup abelian. -/
theorem derived_self_commutator_eq_bot : ⁅DerivedPreimage, DerivedPreimage⁆ = ⊥ := by
  have h : ⁅ThirdCommutator, RootPreimage⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    exact (commutator_mono third_le_center le_rfl).trans
      (commutator_center_left RootPreimage).le
  exact commutator_commutator_eq_bot_of_rotate h
    (by simpa only [commutator_comm DerivedPreimage RootPreimage] using h)

instance derived_isMulCommutative : IsMulCommutative DerivedPreimage :=
  commutator_self_eq_bot_iff.mp derived_self_commutator_eq_bot

instance third_isMulCommutative : IsMulCommutative ThirdCommutator := by
  apply IsMulCommutative.of_comm
  intro x y
  apply Subtype.ext
  exact (mem_center_iff.mp (third_le_center x.property) y).symm

open scoped IsMulCommutative

/-- The mixed commutator data still to be constructed on the actual third term.
Generation refers to the literal subgroup, not an abstract family tag. -/
structure PairingData where
  pairing : Field →+ (Field →+ Additive ThirdCommutator)
  invariant : EightPairing.TorusInvariant pairing
  jacobi : EightPairing.Jacobi pairing
  generates : AddSubgroup.closure {v | ∃ x z, pairing x z = v} = ⊤

end BenderSuzuki.MatrixGroups.SchurCover.EightLocal

end
