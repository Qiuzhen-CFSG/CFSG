module
public import Theory.GroupTheory.NormalizerResidualCentralCover
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PrimeSL2CoverRigidity

/-!
# The prime-SL₂ residual of a marked involution normalizer

In the odd-core containing row, the normalizer of the marked Sylow
involution maps onto the prime-SL₂ quotient by Frattini's argument.
Its embedded solvable residual still surjects. The cyclic fixed part
of the original kernel makes the restricted kernel central, and the
proved rigidity of perfect central covers of SL₂(p), p > 3, removes it.

The resulting equivalence is the restriction of the actual marked
quotient map. No ambient C-component structure is imposed on this
normalizer residual. The final theorem retains the original normal
subgroup, quotient marking, involution and literal Sylow witness.

Source: Aschbacher--Smith, Proposition 9.3.1, printed p.732, reduction
of the nonquasisimple containing row to its prime-linear row.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceOldResidualOddCoreNormalizerCover
variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

/-- The exact residual map to prime-field SL₂ is bijective once the marked
normalizer surjects and the original involution-fixed kernel is cyclic. -/
theorem normalizer_residual_bijective_of_surjective
    (hp : 3 < p) (q : X →* SL(2,ZMod p)) (t : X) (ht : orderOf t = 2)
    (hN : Function.Surjective (q.comp (normalizer (zpowers t : Set X)).subtype))
    (hc : IsCyclic (q.ker ⊓ centralizer ({t} : Set X) : Subgroup X)) :
    let K := (solvableResidual (normalizer (zpowers t : Set X))).map
      (normalizer (zpowers t : Set X)).subtype
    Function.Bijective (q.comp K.subtype) := by
  let K := (solvableResidual (normalizer (zpowers t : Set X))).map
    (normalizer (zpowers t : Set X)).subtype
  let : Group.IsPerfect SL(2,ZMod p) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod p) (by simpa using hp)
  let : Group.IsPerfect K := Group.IsPerfect.map _
  have hs := NormalizerResidualCentralCover.normalizer_residual_surjective_of_surjective
    q (zpowers t) hN
  have hker := NormalizerResidualCentralCover.normalizer_residual_kernel_central q t ht hc
  exact ⟨ChapterA.RankActions.primeSL2CoverRigidity p hp K (q.comp K.subtype) hs hker,hs⟩

/-- Frattini supplies the original normalizer's surjectivity; central-cover
rigidity identifies its actual embedded residual through the given marking. -/
theorem exists_normalizer_residual_equiv_of_center_preimage_sylow
    (hp : 3 < p) (F : Subgroup X) [F.Normal]
    (e : (X ⧸ F) ≃* SL(2,ZMod p))
    (t : X) (ht : orderOf t = 2)
    (hc : IsCyclic (F ⊓ centralizer ({t} : Set X) : Subgroup X))
    (S : Sylow 2 ((center (X ⧸ F)).comap (QuotientGroup.mk' F)))
    (hS : (S : Subgroup ((center (X ⧸ F)).comap (QuotientGroup.mk' F))).map
      ((center (X ⧸ F)).comap (QuotientGroup.mk' F)).subtype = zpowers t) :
    let K := (solvableResidual (normalizer (zpowers t : Set X))).map
      (normalizer (zpowers t : Set X)).subtype
    ∃ a : K ≃* SL(2,ZMod p), ∀ x : K, a x = e (QuotientGroup.mk' F (x : X)) := by
  let q := QuotientGroup.mk' F
  let N := normalizer (zpowers t : Set X)
  let K := (solvableResidual N).map N.subtype
  let : Group.IsPerfect SL(2,ZMod p) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod p) (by simpa using hp)
  let : Group.IsPerfect (X ⧸ F) := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hN : Function.Surjective (q.comp N.subtype) :=
    NormalizerResidualCentralCover.normalizer_surjective_of_center_preimage_sylow
      q (QuotientGroup.mk'_surjective F) S (zpowers t) hS
  let f := e.toMonoidHom.comp q
  have hfker : f.ker = F := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hbij := normalizer_residual_bijective_of_surjective hp f t ht
    (e.surjective.comp hN) (by rwa [hfker])
  exact ⟨MulEquiv.ofBijective (f.comp K.subtype) hbij,fun _ => rfl⟩

end CFSG.Quasithin.Chapter10.SourceOldResidualOddCoreNormalizerCover
