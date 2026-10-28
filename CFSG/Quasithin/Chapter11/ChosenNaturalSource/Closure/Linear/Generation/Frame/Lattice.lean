module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# Lattice transport for the original natural preimage

The quotient map from the chosen elementary module is surjective.  Therefore
the field subspace preimage used by the Chapter 11 source preserves the joins
and meets needed for a three-line frame.  This is kept separate from the
matrix model calculations and from the source lift correction.
Source: the direct frame in Aschbacher–Smith 11.5.7, printed p.781.
-/

open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource

@[expose] public section

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Coordinates

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
variable (c : Coordinates D F)

theorem binarySubspace_sup (U W : Submodule F.Carrier c.Space) :
    c.binarySubspace (U ⊔ W) = c.binarySubspace U ⊔ c.binarySubspace W := by
  unfold binarySubspace
  rw [Submodule.restrictScalars_sup]
  apply Submodule.comap_sup_of_injective c.linearEquiv.injective
  · simp
  · simp

theorem preimage_sup (U W : Submodule F.Carrier c.Space) :
    c.preimage (U ⊔ W) = c.preimage U ⊔ c.preimage W := by
  unfold preimage
  rw [binarySubspace_sup]
  change ((c.binarySubspace U ⊔ c.binarySubspace W).toAddSubgroup.toSubgroup.comap
    D.toCentralQuotient).map V.subtype =
    ((c.binarySubspace U).toAddSubgroup.toSubgroup.comap D.toCentralQuotient).map V.subtype ⊔
      ((c.binarySubspace W).toAddSubgroup.toSubgroup.comap D.toCentralQuotient).map V.subtype
  rw [Submodule.sup_toAddSubgroup]
  have hsub : AddSubgroup.toSubgroup
      ((c.binarySubspace U).toAddSubgroup ⊔ (c.binarySubspace W).toAddSubgroup) =
      (c.binarySubspace U).toAddSubgroup.toSubgroup ⊔
        (c.binarySubspace W).toAddSubgroup.toSubgroup := by
    exact (AddSubgroup.toSubgroup :
      AddSubgroup (D.chosenCentralQuotient) ≃o
        Subgroup (Multiplicative D.chosenCentralQuotient)).map_sup _ _
  rw [hsub]
  have hc := Subgroup.comap_sup_eq D.toCentralQuotient
    ((c.binarySubspace U).toAddSubgroup.toSubgroup)
    ((c.binarySubspace W).toAddSubgroup.toSubgroup)
    (ChosenModule.toCentralQuotient_surjective D)
  rw [← hc]
  rw [Subgroup.map_sup]

theorem preimage_inf (U W : Submodule F.Carrier c.Space) :
    c.preimage (U ⊓ W) = c.preimage U ⊓ c.preimage W := by
  unfold preimage
  rw [show c.binarySubspace (U ⊓ W) = c.binarySubspace U ⊓ c.binarySubspace W by
    unfold binarySubspace
    rw [Submodule.restrictScalars_inf]
    rfl]
  change ((c.binarySubspace U ⊓ c.binarySubspace W).toAddSubgroup.toSubgroup.comap
    D.toCentralQuotient).map V.subtype =
    ((c.binarySubspace U).toAddSubgroup.toSubgroup.comap D.toCentralQuotient).map V.subtype ⊓
      ((c.binarySubspace W).toAddSubgroup.toSubgroup.comap D.toCentralQuotient).map V.subtype
  have hinf : (c.binarySubspace U ⊓ c.binarySubspace W).toAddSubgroup.toSubgroup =
      (c.binarySubspace U).toAddSubgroup.toSubgroup ⊓
        (c.binarySubspace W).toAddSubgroup.toSubgroup := by rfl
  rw [hinf]
  rw [← Subgroup.map_inf_eq _ _ V.subtype V.subtype_injective]
  rw [Subgroup.comap_inf]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Coordinates
