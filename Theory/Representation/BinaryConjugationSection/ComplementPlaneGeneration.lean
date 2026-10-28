module
public import Theory.Representation.BinaryParabolicExteriorSquare.ComplementCubic
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages
public import Theory.LinearAlgebra.BinaryFlagCoordinates
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Generation modulo a marked plane by a complementary cubic

In a binary natural four-space the cubic fixing the first plane has full
image on its complementary plane. Lifting this displacement through the
original conjugation coordinates gives U = V₃ [U,D], with the full kernel
V₁ retained. No ambient containment of U in D is assumed.

Source application: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.30, printed p.964. This supplies the seed commutator relation used to
place the original L-span inside L before constructing its chief quotient.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
open BinaryParabolicExteriorSquare.PlaneSpan BinaryLinear.FlagCoordinates
variable {G : Type*} [Group G]

/-- A complementary-plane cubic generates the original section modulo the
marked plane, through the unchanged coordinate map. -/
theorem section_eq_plane_sup_commutator_of_complement
    (H D U V1 V3 : Subgroup G) (hDH : D ≤ H)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H U V1 ρ)
    (π : H →* SL(4,ZMod 2))
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (h13 : V1 ≤ V3) (h3U : V3 ≤ U) (hplane : d.imageSpace V3 = plane)
    (hcubic : complementElement ∈ (D.subgroupOf H).map π) :
    U = V3 ⊔ ⁅U,D⁆ := by
  obtain ⟨a,ha,he⟩ := hcubic
  have hcU : ⁅U,D⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (hDH.trans d.normalized)
  have hfull : d.imageSpace (V3 ⊔ ⁅U,D⁆) = ⊤ := by
    apply top_unique
    intro w _
    let y : Fin 4 → ZMod 2 := ![0,0,w 3,w 2 + w 3]
    have hp : w - (ρ a y - y) ∈ plane := by
      rw [hnatural,he]
      change (w 2 - (Matrix.mulVec complementCubic y 2 - y 2) = 0) ∧
        (w 3 - (Matrix.mulVec complementCubic y 3 - y 3) = 0)
      constructor <;>
        simp [complementCubic,y,Matrix.mulVec,dotProduct,
          Fin.sum_univ_succ,sub_eq_add_neg,ZMod.neg_eq_self_mod_two,
          add_assoc,CharTwo.add_self_eq_zero,CharTwo.add_cancel_left]
    have hd : ρ a y - y ∈ d.imageSpace ⁅U,D⁆ := by
      rw [commutator_comm U D,d.imageSpace_commutator D U hDH le_rfl,
        d.imageSpace_self]
      exact Submodule.subset_span ⟨a,ha,y,Submodule.mem_top,rfl⟩
    have hp' : w - (ρ a y - y) ∈ d.imageSpace (V3 ⊔ ⁅U,D⁆) :=
      d.imageSpace_mono le_sup_left (hplane.symm ▸ hp)
    have hd' := d.imageSpace_mono (le_sup_right : ⁅U,D⁆ ≤ V3 ⊔ ⁅U,D⁆) hd
    simpa only [sub_add_cancel] using (d.imageSpace _).add_mem hp' hd'
  apply le_antisymm ?_ (sup_le h3U hcU)
  calc U = d.subspacePreimage ⊤ := by
         rw [←d.imageSpace_self,d.subspacePreimage_imageSpace U le_rfl d.kernel_le]
       _ ≤ V3 ⊔ ⁅U,D⁆ :=
         d.subspacePreimage_le_of_imageSpace_le ⊤ _ (h13.trans le_sup_left) hfull.ge

end Representation.BinaryConjugationSection
