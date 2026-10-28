module

public import Theory.SpecificGroups.Monster.Construction.LocalEmbedding
public import Theory.SpecificGroups.Monster.Construction.LocalC.TensorKernel
public import Theory.AtlasPort.OtherSporadic.Conway.LeechCentralQuotient

/-!
# The local Monster projection to the lattice Conway quotient

The pullback's Leech projection kills the tensor kernel after quotienting
by scalar signs. It therefore descends to the actual group C and its
faithful image in the fixed Griess group. The representative equations
retain the original lattice isometry. Surjectivity is reduced to lifting
Leech isometries to the spin–Leech pullback; it is not assumed here.

Source: Aschbacher, *Sporadic Groups*, 27.5–27.9 and 28.12–28.13.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.QuasithinObstruction
open LocalC Atlas.Conway Atlas.Lattices

def pullbackLeech : localPullback →* LeechIsometryGroup :=
  (MonoidHom.snd _ _).comp localPullback.subtype

def pullbackQuotient : localPullback →* LeechCentralQuotient :=
  leechCentralProjection.comp pullbackLeech

theorem tensor_kernel_le_quotient_kernel : pullbackToC.ker ≤ pullbackQuotient.ker := by
  intro x hx
  have he := (pullbackTensor_kernel_iff x).mp (congrArg Subtype.val hx)
  change leechCentralProjection x.val.2 = 1
  change x.val.2 ∈ leechCentralProjection.ker
  rw [leechCentralProjection_kernel, leechCentralSigns_mem]
  exact he.imp And.left And.left

def cToLeechQuotient : C →* LeechCentralQuotient :=
  tensorDescend pullbackQuotient tensor_kernel_le_quotient_kernel

@[simp] theorem cToLeechQuotient_pullback (x : localPullback) :
    cToLeechQuotient (pullbackToC x) = leechCentralProjection x.val.2 :=
  tensorDescend_pullback _ _ x

def localToLeechQuotient : localSubgroup →* LeechCentralQuotient :=
  cToLeechQuotient.comp cEquivLocalSubgroup.symm.toMonoidHom

@[simp] theorem localToLeechQuotient_c (c : C) :
    localToLeechQuotient (cEquivLocalSubgroup c) = cToLeechQuotient c := by
  change cToLeechQuotient (cEquivLocalSubgroup.symm (cEquivLocalSubgroup c)) = _
  rw [cEquivLocalSubgroup.symm_apply_apply]

theorem cToLeechQuotient_surjective_of_pullback
    (h : Function.Surjective pullbackLeech) : Function.Surjective cToLeechQuotient := by
  intro y
  obtain ⟨g, rfl⟩ := leechCentralProjection_surjective y
  obtain ⟨x, rfl⟩ := h g
  exact ⟨pullbackToC x, cToLeechQuotient_pullback x⟩

open TrialitySpin

@[simp] theorem cToLeechQuotient_n1 (g : N1) :
    cToLeechQuotient (n1ToC g) = leechCentralProjection (n1LeechRepresentation g) :=
  cToLeechQuotient_pullback (n1Pullback g)

@[simp] theorem cToLeechQuotient_z1C : cToLeechQuotient z1C = 1 := by
  change cToLeechQuotient (n1ToC SpinAction.z) = 1
  rw [cToLeechQuotient_n1, n1LeechRepresentation_z, map_one]

@[simp] theorem localToLeechQuotient_pullback (x : localPullback) :
    localToLeechQuotient (cEquivLocalSubgroup (pullbackToC x)) =
      leechCentralProjection x.val.2 := by
  rw [localToLeechQuotient_c, cToLeechQuotient_pullback]

@[simp] theorem localToLeechQuotient_z1C :
    localToLeechQuotient (cEquivLocalSubgroup z1C) = 1 := by
  rw [localToLeechQuotient_c, cToLeechQuotient_z1C]
end Sporadic.Monster.Construction.QuasithinObstruction
