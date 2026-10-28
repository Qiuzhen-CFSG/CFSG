module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The genuine natural-module identification in K.3.6

The group equivalence identifies the entire marked layer with the concrete
Suzuki group. The binary linear equivalence intertwines its literal matrix
action; neither dimensions nor ratio conclusions are supplied as hypotheses.
Recognition of this identification belongs to the rank-one recognition proof.

Source: Aschbacher–Smith, K.3.6, printed p.457 (1 March 2004 manuscript).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.RankOne
open BenderSuzuki BenderSuzuki.MatrixGroups PFAppendixIII Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The specified layer acts as the natural four-dimensional Suzuki module. -/
structure SuzukiModel (m : ℕ) (ρ : Representation (ZMod 2) G V) (L : Subgroup G) where
  groupEquiv : L ≃* SuzukiMatrixGroup m
  coordinates : V ≃ₗ[ZMod 2] (Fin 4 → BinaryGaloisField (2 * m + 1))
  intertwines : ∀ (g : L) (v : V),
    coordinates (ρ (g : G) v) = Matrix.mulVec (groupEquiv g).val.val (coordinates v)

namespace SuzukiModel
variable {m : ℕ} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (M : SuzukiModel m ρ L)

/-- Changing coordinates keeps the original ambient actor. -/
noncomputable def coordinateAction : Representation (ZMod 2) G (Fin 4 → BinaryGaloisField (2 * m + 1)) :=
  M.coordinates.conjRingEquiv.toMonoidHom.comp ρ

@[simp] theorem coordinateAction_apply (g : G) (v : V) :
    M.coordinateAction g (M.coordinates v) = M.coordinates (ρ g v) := by
  change M.coordinates (ρ g (M.coordinates.symm (M.coordinates v))) = _
  rw [M.coordinates.symm_apply_apply]

theorem coordinateAction_natural (g : L) (v : Fin 4 → BinaryGaloisField (2 * m + 1)) :
    M.coordinateAction (g : G) v = Matrix.mulVec (M.groupEquiv g).val.val v := by
  change M.coordinates (ρ (g : G) (M.coordinates.symm v)) = _
  rw [M.intertwines, M.coordinates.apply_symm_apply]

include M in
theorem finrank_eq : Module.finrank (ZMod 2) V = 4 * (2 * m + 1) := by
  rw [M.coordinates.finrank_eq, Module.finrank_pi_fintype]
  simp [GaloisField.finrank 2 (by omega : 2 * m + 1 ≠ 0)]

theorem fixedCodim_eq (A : Subgroup G) :
    fixedCodim ρ A = fixedCodim M.coordinateAction A := by
  simpa using fixedCodim_map_equivariant ρ M.coordinateAction (MonoidHom.id G)
    M.coordinates (fun g v => (M.coordinateAction_apply g v).symm) A

end SuzukiModel
end CFSG.Quasithin.ChapterK.RankOne
