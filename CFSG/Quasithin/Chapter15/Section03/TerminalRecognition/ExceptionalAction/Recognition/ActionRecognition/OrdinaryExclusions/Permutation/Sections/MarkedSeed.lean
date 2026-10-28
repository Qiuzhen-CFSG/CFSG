module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.GroupTheory.SylowKernelCore

/-!
# The marked residual action on the projected seed

Inclusion into the moved subrepresentation and the actual central projection
intertwine the full quotient action. Consequently the image of the original
seed is fixed by the two-core of the literal image of Y_F and is generated
by commutators with that same residual. The group identification is exactly
the one in the natural section, so these statements apply to its transported
parabolics. Together with `seedMap_range_finrank`, they supply all hypotheses
of the concrete six- and seven-point residual obstructions.

Only the seed must inject into the central quotient; no splitting of the
ambient module is required.

Source: Aschbacher–Smith, B.5.1/B.5.6, printed pp.99 and 105, and the final
proof of 15.3.1, printed p.1155 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] {d : SourceInput V}
namespace NaturalSection
variable {n : ℕ} (s : NaturalSection d n)

private noncomputable def sectionMap :
    s.sectionData.space.toSubmodule →ₗ[ZMod 2] BinaryPermutation.natural (Fin n) :=
  s.natural.linearEquiv.toLinearMap.comp s.sectionData.central.toSubmodule.mkQ

omit [Finite H] in
private theorem sectionMap_intertwines (g : coreQuotient H)
    (v : s.sectionData.space.toSubmodule) :
    sectionMap s (s.sectionData.space.toRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin n) (s.natural.groupEquiv g) (sectionMap s v) :=
  s.natural.intertwines g (s.sectionData.central.toSubmodule.mkQ v)

omit [Finite H] in
private theorem seedMap_range_eq : LinearMap.range s.seedMap =
    ((planeSubspace V V).comap s.sectionData.space.toSubmodule.subtype).map (sectionMap s) := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨Submodule.inclusion s.vector_le_space v, v.property, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

/-- The marked residual core still fixes the projected seed, under the
same full-quotient coordinates as the natural action. -/
theorem seedMap_range_fixed : LinearMap.range s.seedMap ≤
    fixedSpace (BinaryPermutation.naturalRepresentation (Fin n))
      ((d.YF.map (s.natural.groupEquiv.toMonoidHom.comp coreProjection)).pCoreIn 2) := by
  rw [seedMap_range_eq, ← Subgroup.map_map,
    ← map_pCoreIn_of_injective 2 _ _ s.natural.groupEquiv.injective]
  rintro _ ⟨v, hv, rfl⟩ ⟨_, g, hg, rfl⟩
  change BinaryPermutation.naturalRepresentation (Fin n) (s.natural.groupEquiv g)
    (sectionMap s v) = sectionMap s v
  rw [← sectionMap_intertwines]
  congr 1
  apply Subtype.ext
  exact d.vector_fixed hv ⟨g, hg⟩

omit [Finite H] in
/-- Residual commutators generate the projected seed. This remains necessary
when the model residual has trivial two-core, as can happen in degree seven. -/
theorem seedMap_range_commutator :
    subspaceCommutator (BinaryPermutation.naturalRepresentation (Fin n))
      (LinearMap.range s.seedMap)
      (d.YF.map (s.natural.groupEquiv.toMonoidHom.comp coreProjection)) =
        LinearMap.range s.seedMap := by
  let P := planeSubspace V V
  let U := P.comap s.sectionData.space.toSubmodule.subtype
  let L := d.YF.map coreProjection
  have hmap : U.map s.sectionData.space.toSubmodule.subtype = P := by
    exact Submodule.map_comap_eq_of_le (by simpa using s.vector_le_space)
  have hU : subspaceCommutator s.sectionData.space.toRepresentation U L = U := by
    apply Submodule.map_injective_of_injective s.sectionData.space.toSubmodule.injective_subtype
    rw [hmap]
    have he := subspaceCommutator_map_embedding
      (quotientAction V d.centralizer_isTwoGroup d.core_centralizes)
      s.sectionData.space.toRepresentation (MonoidHom.id _) s.sectionData.space.toSubmodule.subtype
      (fun _ _ => rfl) L U
    calc
      _ = subspaceCommutator
          (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) P L := by
        simpa only [Subgroup.map_id, hmap] using he.symm
      _ = P := vector_subspaceCommutator d
  rw [seedMap_range_eq, ← Subgroup.map_map]
  change subspaceCommutator (BinaryPermutation.naturalRepresentation (Fin n))
    (U.map (sectionMap s)) (L.map s.natural.groupEquiv.toMonoidHom) = U.map (sectionMap s)
  have he := subspaceCommutator_map_embedding
    (BinaryPermutation.naturalRepresentation (Fin n)) s.sectionData.space.toRepresentation
    s.natural.groupEquiv.symm.toMonoidHom (sectionMap s)
    (fun g v => by simpa using (sectionMap_intertwines s (s.natural.groupEquiv.symm g) v).symm)
    (L.map s.natural.groupEquiv.toMonoidHom) U
  have hL : (L.map s.natural.groupEquiv.toMonoidHom).map
      s.natural.groupEquiv.symm.toMonoidHom = L := by
    rw [Subgroup.map_map]
    simp
  rwa [hL, hU] at he
end NaturalSection

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
