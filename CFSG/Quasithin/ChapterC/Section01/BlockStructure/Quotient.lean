module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PResidual.PerfectLift
public import Theory.GroupTheory.CentralPPerfectCoprime
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The central quotient of a short group

The canonical map X/U(X) → X/O₂(X) has central two-group kernel. In the
quasisimple case, two-perfection makes its domain perfect, hence
quasisimple. In the order-three case, the central-kernel rigidity theorem
makes the map an isomorphism. These are exactly the alternatives in
Aschbacher--Smith C.1.8, combined manuscript of 1 March 2004, printed p.123.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L]

/-- The canonical map from X/U(X) onto X/O₂(X). -/
@[expose] def blockCoreProjection : (L ⧸ blockU L) →* (L ⧸ pCore 2 L) :=
  QuotientGroup.lift (blockU L) (QuotientGroup.mk' (pCore 2 L))
    (by simpa using (blockU_le_core (L := L)))

theorem blockCoreProjection_ker : (blockCoreProjection (L := L)).ker =
    (pCore 2 L).map (QuotientGroup.mk' (blockU L)) := by
  rw [blockCoreProjection, QuotientGroup.ker_lift, QuotientGroup.ker_mk']

theorem blockCoreProjection_surjective : Function.Surjective (blockCoreProjection (L := L)) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective _) _

/-- Aschbacher--Smith C.1.8: the quotient by U is quasisimple or has order three. -/
theorem IsShort.quotient_blockU (h : IsShort L) :
    IsQuasisimple (L ⧸ blockU L) ∨ Nat.card (L ⧸ blockU L) = 3 := by
  let := h.finite
  let f := blockCoreProjection (L := L)
  have hf : Function.Surjective f := blockCoreProjection_surjective
  have hc : f.ker ≤ center (L ⧸ blockU L) := by
    rw [blockCoreProjection_ker]
    exact blockU_core_image_le_center
  have hp : IsPGroup 2 f.ker := by
    rw [blockCoreProjection_ker]
    exact pCore_isPGroup.map _
  rcases h.quotient with hs | hs
  · let := hs
    let := IsPPerfect.isPerfect_of_surjective_pGroup_kernel (h.quotient_twoPerfect (blockU L)) f hf hp
    left
    exact PerfectCentralCovering.Cover.isQuasisimple
      { toMonoidHom := f, surjective := hf, ker_le_center := hc, isPerfect := inferInstance }
  · right
    let : IsCyclic (L ⧸ pCore 2 L) := isCyclic_of_prime_card hs
    let : CommGroup (L ⧸ pCore 2 L) := IsMulCommutative.instCommGroup
    have hi : Function.Injective f :=
      f.injective_of_isPPerfect_of_coprime_abelian_image
        (h.quotient_twoPerfect (blockU L)) hc hp (fun x y => Commute.all _ _)
        (by decide : Nat.Coprime 2 3) (fun x => by
          rw [← hs]
          exact pow_card_eq_one')
    exact (Nat.card_congr (Equiv.ofBijective f ⟨hi, hf⟩)).trans hs
end CFSG.Quasithin.ChapterC
