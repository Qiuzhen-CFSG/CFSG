module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.SymmetricSix
public import Theory.Representation.BinaryPermutationSixCover.Twisted
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.AugmentationKernel.AlternatingCover
public import Theory.Representation.BinaryOffender.QuadraticQuotient
/-!
# Fixed-kernel movement in the natural symmetric-six quotient

B.5 selects a marked natural quotient for a faithful strict offender module.
Its actor still has fixed codimension two on that quotient. The universal
alternating augmentation cover and its even-actor displacement therefore put
the literal component fixed space inside the original actor movement.

Source: Aschbacher--Smith B.5.1 and I.1.5–6; MS93 (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
local notation "S6" => Equiv.Perm (Fin 6)
local notation "A6" => alternatingGroup (Fin 6)

theorem symmetricSix_natural_quotient_fixed_le_moved
    (ρ : Representation (ZMod 2) S6 V) (hf : Function.Injective ρ)
    (hsq : IsSQTK KnownSimple.IsKnownSimple A6)
    (A : Subgroup S6) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 8) (hc : fixedCodim ρ A = 2) (hodd : ¬ A ≤ A6)
    (hm : subspaceCommutator ρ ⊤ A6 = ⊤) :
    ∃ (e : S6 ≃* S6) (p : V →ₗ[ZMod 2] natural (Fin 6)),
      Function.Surjective p ∧ p.ker = fixedSpace ρ A6 ∧
      (∀ g v, p (ρ g v) = naturalRepresentation (Fin 6) (e g) (p v)) ∧
      fixedSpace ρ A6 ≤ subspaceCommutator ρ ⊤ A := by
  obtain ⟨e,p,hp,hk,he⟩ := symmetricSix_natural_quotient ρ hf hsq A hA hc hodd hm
  have hcod : fixedCodim (naturalRepresentation (Fin 6)) (A.map e.toMonoidHom) ≤ 2 := by
    have hh := fixedCodim_le_of_equivariant_surjection ρ
      ((naturalRepresentation (Fin 6)).comp e.toMonoidHom) p hp he A
    rw [hc] at hh
    unfold fixedCodim at hh ⊢
    rwa [fixedSpace_comp_map] at hh
  let : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hAc : Nat.card (A.map e.toMonoidHom) = 8 :=
    (card_map_of_injective e.injective).trans hA
  have hcod2 := (AlternatingSixInvolutionDisplacement.strict_small_elementary_card
    (naturalRepresentation (Fin 6)) (naturalRepresentation_injective (Fin 6) (by decide))
    (A.map e.toMonoidHom) hAc.le (by
      rw [hAc]
      have hp2 := Nat.pow_le_pow_right (by decide : 0 < 2) hcod
      omega)).2
  obtain ⟨f,hf0,hfe,hpf⟩ := SixCover.core_surjection_of_twisted_cover ρ e p hp he hk.le hm
  have hmov := ChapterB.Offenders.Six.alternating_cover_kernel_le_moved
    ρ e A hA hcod2 f hf0 hfe p hpf
  exact ⟨e,p,hp,hk,he,hk ▸ hmov⟩
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
