module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction.Placement.Transport
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction.Placement.Alignment
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction.Placement.Construction

/-!
# Marked placement for the cubic argument

The original involution maps into the specified M₁₀, so `Alignment` supplies
an actual permutation identifying it with the canonical semidihedral center.
`Construction` lifts the corresponding complement through the cubic kernel
and places it in the literal intersection T_R = N_{T_+}(R). `Transport` then
supplies its generators, their presentation, the standard-model equivalence,
and the two actual transposition markings.

`exists_marked_placement` assembles these results from the marked Aut(A₆)
quotient and centralizer image alone. Neither an alignment nor a lift is an
input. Its normalizer equality retains actual product factors and the Sylow
two-subgroup whose ambient image is T_R. The earlier source inputs and the
subsequent action and point-orbit arguments remain with their assembly owners.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

public section

namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction.Placement
open Subgroup
open scoped Pointwise
open AlternatingSix.ShadowLocal
open AlternatingSix.M10.LocalGeometry

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- Both missing premises of the generator transport are constructed from the
source's quotient marking, with the actual conjugating permutation retained. -/
theorem exists_aligned_lift (hB : Nat.card c.B = 3) (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* AutA6)
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension) :
    ∃ σ : Equiv.Perm (Fin 6),
      markedMap c e (zInNB c) =
        (MulAut.conj (permutationAction σ)) (permutationAction (standardU * standardZ)) ∧
      Nonempty (Lift c e σ) := by
  obtain ⟨σ, hσ⟩ := exists_marked_z_alignment c hB hz e hM
  exact ⟨σ, hσ, Construction.exists_lift c hB hz e σ hσ⟩

/-- The source normalizer is the literal ordered product R T_R as a set. -/
theorem Lift.normalizer_setwise_product
    {e : c.NormalizerQuotient ≃* AutA6} {σ : Equiv.Perm (Fin 6)}
    (l : Lift c e σ) (hB : Nat.card c.B = 3) :
    ((c.NB ⊓ normalizer (ambient c l.R : Set G) : Subgroup G) : Set G) =
      (ambient c l.R : Set G) * (TR c l.R l.Tplus : Set G) := by
  ext x
  exact l.normalizer_product hB x

/-- The complete marked semidihedral placement in the cubic normalizer.
The first and second swaps are respectively σ(02)σ⁻¹ and σ(13)σ⁻¹, so
their markings use the original quotient map rather than an abstract action. -/
theorem exists_marked_placement (hB : Nat.card c.B = 3) (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* AutA6)
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension) :
    ∃ (σ : Equiv.Perm (Fin 6)) (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
      (r f : TR c R Tplus),
      orderOf r = 8 ∧
      orderOf f = 2 ∧
      f * r * f⁻¹ = r ^ 3 ∧
      closure ({r, f} : Set (TR c R Tplus)) = ⊤ ∧
      (r : G) ^ 4 = c.z ∧
      c.z ∈ TR c R Tplus ∧
      Nat.card (TR c R Tplus) = 16 ∧
      Nonempty (TR c R Tplus ≃* Semidihedral.StandardModel 4 (by decide)) ∧
      (center (TR c R Tplus)).map (TR c R Tplus).subtype = zpowers c.z ∧
      orderOf (f : G) = 2 ∧
      orderOf ((f : G) * c.z) = 2 ∧
      (Lift.firstSwap (σ := σ)).IsSwap ∧
      (Lift.secondSwap (σ := σ)).IsSwap ∧
      markedMap c e (inclusion (TR_le_NB c R Tplus) f) =
        permutationAction (Lift.firstSwap (σ := σ)) ∧
      markedMap c e ((inclusion (TR_le_NB c R Tplus) f) * zInNB c) =
        permutationAction (Lift.secondSwap (σ := σ)) ∧
      ((c.NB ⊓ normalizer (ambient c R : Set G) : Subgroup G) : Set G) =
        (ambient c R : Set G) * (TR c R Tplus : Set G) ∧
      (∀ x : G, x ∈ c.NB ⊓ normalizer (ambient c R : Set G) ↔
        ∃ a ∈ ambient c R, ∃ t ∈ TR c R Tplus, a * t = x) ∧
      ∃ S : Sylow 2 ↥(c.NB ⊓ normalizer (ambient c R : Set G)),
        (S : Subgroup ↥(c.NB ⊓ normalizer (ambient c R : Set G))).map
          (c.NB ⊓ normalizer (ambient c R : Set G)).subtype = TR c R Tplus := by
  obtain ⟨σ, hσ, ⟨l⟩⟩ := exists_aligned_lift c hB hz e hM
  exact ⟨σ, l.R, l.Tplus, l.rotation, l.flip,
    l.rotation_order, l.flip_order, l.flip_rotation, l.generated,
    l.rotation_four hσ, l.z_mem, l.card, ⟨l.semidihedralEquiv⟩,
    l.embedded_center hσ, l.flip_ambient_order, l.flip_z_order hσ,
    Lift.firstSwap_isSwap, Lift.secondSwap_isSwap, l.marked_flip, l.marked_flip_z hσ,
    l.normalizer_setwise_product c hB, l.normalizer_product hB, l.exists_sylow_two hB⟩

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction.Placement
