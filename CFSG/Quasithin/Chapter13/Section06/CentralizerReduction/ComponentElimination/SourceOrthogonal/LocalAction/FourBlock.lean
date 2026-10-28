module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction
public import Theory.SpecificGroups.SymmetricEight.FourBlockResidual

/-!
# The marked four-block source consumer

This module performs the final source transport once the marked action has
identified the component image with A₈, the seed stabilizer with the literal
four-block stabilizer, and the image of Tᵥ with the chosen Sylow-two subgroup.
The residual equality and the wreath action are explicit inputs at their
mathematical interfaces; the theorem below derives the image equality used by
the quotient transport before applying the concrete quotient equivalence.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction

open ComponentSelection
open Theory.SpecificGroups.SymmetricEight
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Theory.SpecificGroups.SymmetricEight.FourBlockResidual

variable {G : Type*} [Group G] [Finite G]

variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- The source XTᵥ has the marked four-block image, hence its two-core is the
literal Klein group and its quotient is the regular two-block wreath product. -/
noncomputable def sourceWreathQuotient
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker)
    (e : Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8))
    (hC : (plusImage K L T z v hL hz K).map e.toMonoidHom =
      alternatingGroup (Fin 8))
    (hseed : (seedStabilizer K L T z v hL hz).map e.toMonoidHom =
      A6ShadowTwoLocals.fourStabilizer)
    (hres :
      (primeToResidual 3
        (alternatingGroup (Fin 8) ⊓ A6ShadowTwoLocals.fourStabilizer :
          Subgroup (Equiv.Perm (Fin 8)))).map
        (alternatingGroup (Fin 8) ⊓
          A6ShadowTwoLocals.fourStabilizer).subtype =
        fourBlockResidual)
    (S : Subgroup (Equiv.Perm (Fin 8)))
    (hTv :
      (plusImage K L T z v hL hz (Tv T v)).map e.toMonoidHom = S)
    (hgen : fourBlockResidual ⊔ S =
      A6ShadowTwoLocals.fourStabilizer)
    (φ : FourBlockResidual.H →* FourBlockResidual.W)
    (hker : φ.ker = pCore 2 FourBlockResidual.H)
    (hsurj : Function.Surjective φ) :
    (Source.orthogonalResidual K z ⊔ Tv T v : Subgroup G) ⧸
        pCore 2 (Source.orthogonalResidual K z ⊔ Tv T v : Subgroup G) ≃*
      FourBlockResidual.W := by
  have hX : Source.orthogonalResidual K z ≤ plusActor K L T v :=
    (map_subtype_le _).trans (inf_le_left.trans (K_le_plusActor K L T v))
  have himage :
      (plusImage K L T z v hL hz
        (Source.orthogonalResidual K z ⊔ Tv T v)).map e.toMonoidHom =
        A6ShadowTwoLocals.fourStabilizer := by
    rw [plusImage_sup K L T z v hL hz
      (Source.orthogonalResidual K z) (Tv T v) hX le_sup_right,
      Subgroup.map_sup]
    have hR := residual_image_of_seed_marking K L T z v hL hz e hC hseed
    rw [hR, hres, hTv, hgen]
  exact (fourBlockQuotientEquiv K L T z v hL hz hk e himage).trans
    (quotientWreathEquiv φ hker hsurj)

/-- The source quotient map keeps the representative formula from the
original plus map before the final wreath descent. -/
theorem sourceWreathQuotient_mk
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker)
    (e : Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8))
    (hC : (plusImage K L T z v hL hz K).map e.toMonoidHom =
      alternatingGroup (Fin 8))
    (hseed : (seedStabilizer K L T z v hL hz).map e.toMonoidHom =
      A6ShadowTwoLocals.fourStabilizer)
    (hres :
      (primeToResidual 3
        (alternatingGroup (Fin 8) ⊓ A6ShadowTwoLocals.fourStabilizer :
          Subgroup (Equiv.Perm (Fin 8)))).map
        (alternatingGroup (Fin 8) ⊓
          A6ShadowTwoLocals.fourStabilizer).subtype =
        fourBlockResidual)
    (S : Subgroup (Equiv.Perm (Fin 8)))
    (hTv :
      (plusImage K L T z v hL hz (Tv T v)).map e.toMonoidHom = S)
    (hgen : fourBlockResidual ⊔ S =
      A6ShadowTwoLocals.fourStabilizer)
    (φ : FourBlockResidual.H →* FourBlockResidual.W)
    (hker : φ.ker = pCore 2 FourBlockResidual.H)
    (hsurj : Function.Surjective φ)
    (x : (Source.orthogonalResidual K z ⊔ Tv T v : Subgroup G)) :
    sourceWreathQuotient K L T z v hL hz hk e hC hseed hres S hTv hgen
        φ hker hsurj (QuotientGroup.mk x) =
      (quotientWreathEquiv φ hker hsurj
        (fourBlockQuotientEquiv K L T z v hL hz hk e
          (by
            have hX : Source.orthogonalResidual K z ≤ plusActor K L T v :=
              (map_subtype_le _).trans
                (inf_le_left.trans (K_le_plusActor K L T v))
            rw [plusImage_sup K L T z v hL hz
              (Source.orthogonalResidual K z) (Tv T v) hX le_sup_right,
              Subgroup.map_sup]
            have hR := residual_image_of_seed_marking K L T z v hL hz e hC hseed
            rw [hR, hres, hTv, hgen])
        (QuotientGroup.mk x))) := by rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction
