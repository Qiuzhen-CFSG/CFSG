module

public import Theory.SpecificGroups.LieType.A02ParabolicSections

/-!
# Projected faithful subgroups have their own central quotients as sections

Let f : L → C be injective. The kernel of L → C/Z(C) is contained in Z(L),
since its elements commute with every f(x). Thus the actual projected image
surjects onto L/Z(L). This needs no assertion that f(Z(L)) lies in Z(C),
and does not identify the two central quotients as subgroups.

The final constructor puts this explicit surjection into a proper two-local
normalizer. Its source application in `EvenLie.ExceptionalSections` uses
the literal Sp₆(2) matrix group before taking its central quotient.

Source: the central-version distinctions for subsystem groups in GLS3 §2.6,
used by Aschbacher–Smith A.2.18, printed p.40 of `refs/quasithin.pdf`.
-/

@[expose] public section

namespace Theory.SpecificGroups.LieType
open Subgroup
namespace CentralImage
variable {L C : Type*} [Group L] [Group C]

/-- The representation followed by the literal ambient central projection. -/
def projectedHom (f : L →* C) : L →* C ⧸ center C :=
  (QuotientGroup.mk' (center C)).comp f

theorem projectedHom_ker_le (f : L →* C) (hf : Function.Injective f) :
    (projectedHom f).ker ≤ center L := by
  intro x hx
  have hc : f x ∈ center C := (QuotientGroup.eq_one_iff _).mp hx
  apply mem_center_iff.mpr
  intro y
  apply hf
  simpa only [map_mul] using mem_center_iff.mp hc (f y)

/-- The actual projected image maps onto the source's central quotient. -/
noncomputable def quotientMap (f : L →* C) (hf : Function.Injective f) :
    (projectedHom f).range →* L ⧸ center L :=
  (QuotientGroup.lift (projectedHom f).ker (QuotientGroup.mk' (center L))
    (fun x hx => (QuotientGroup.eq_one_iff x).mpr (projectedHom_ker_le f hf hx))).comp
      (QuotientGroup.quotientKerEquivRange (projectedHom f)).symm.toMonoidHom

/-- Both projective markings agree on every original representative. -/
@[simp] theorem quotientMap_apply (f : L →* C) (hf : Function.Injective f) (x : L) :
    quotientMap f hf ((projectedHom f).rangeRestrict x) = QuotientGroup.mk' (center L) x := by
  have he : (QuotientGroup.quotientKerEquivRange (projectedHom f)).symm
      ((projectedHom f).rangeRestrict x) = QuotientGroup.mk' (projectedHom f).ker x := by
    apply (MulEquiv.symm_apply_eq _).mpr
    rfl
  dsimp only [quotientMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [he]
  rfl

theorem quotientMap_surjective (f : L →* C) (hf : Function.Injective f) :
    Function.Surjective (quotientMap f hf) := by
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) z
  exact ⟨(projectedHom f).rangeRestrict x, quotientMap_apply f hf x⟩

end CentralImage

namespace NormalizerSection
variable {L C : Type*} [Group L] [Group C]

/-- A faithful matrix-level Levi map yields the required projective section
once its actual projected range lies in the specified proper normalizer. -/
noncomputable def ofCentralEmbedding (Q : Subgroup (C ⧸ center C))
    (hQ : Q ≠ ⊥) (h₂ : IsPGroup 2 Q)
    (hproper : Subgroup.normalizer (Q : Set (C ⧸ center C)) ≠ ⊤)
    (f : L →* C) (hf : Function.Injective f)
    (hU : (CentralImage.projectedHom f).range ≤
      Subgroup.normalizer (Q : Set (C ⧸ center C))) :
    NormalizerSection (C ⧸ center C) (L ⧸ center L) :=
  ofSurjection Q (CentralImage.projectedHom f).range hQ h₂ hproper hU
    (CentralImage.quotientMap f hf) (CentralImage.quotientMap_surjective f hf)

end NormalizerSection
end Theory.SpecificGroups.LieType
