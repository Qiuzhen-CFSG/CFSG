module

public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeSource
public import Theory.Representation.BinaryPermutation.SixDeletedFixed
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The native inner A6 hexad action

The natural four-space intertwiner restricts through the surjective inner
A6 marking, proving inner irreducibility. The distinct six-coordinate marking
gives the permutation core quotient. Its deleted dual has no A6 fixed vector;
since every cocode vector fixed by the stabilizer is fixed by its kernel,
this proves full code displacement under the inner hexad stabilizer.
The inner and outer kernels have the same literal image in the pair group,
so the five-space, fixed quotient and full transvections keep the native
inner action. Source: Aschbacher--Smith H.16.4 and 8.2.11, pp.403,722.
-/

@[expose] public noncomputable section
open Sporadic.Mathieu MathieuCode MathieuCode.Hexad
open MathieuCode.Hexad.ChiefFlag MathieuCode.Hexad.ChiefFlag.Actions
open Representation Representation.BinaryOffender
open M22ChapterH.Hexad.Action
namespace CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeInner
open NativeSource

/-- Inner irreducibility follows from the natural A6 module and its surjective marking. -/
theorem naturalFour_irreducible :
    IsIrreducible (codeCenter.quotientRepresentation.comp innerToOuter) :=
  irreducible_transport _ (BinaryPermutation.alternatingNaturalRepresentation (Fin 6))
    Natural.innerMap Natural.innerMap_surjective naturalFourEquiv
    naturalFourEquiv_inner_equivariant
    (BinaryPermutation.alternatingNatural_isIrreducible (by decide))

/-- The six-coordinate A6 marking; it is kept distinct from the natural kernel marking. -/
def permutationMap : Inner →* alternatingGroup (Fin 6) :=
  Assembly.coordinateNumbering.altCongrHom.toMonoidHom.comp
    (M22ChapterH.Hexad.innerQuotientEquiv.toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 Inner)))

theorem permutationMap_surjective : Function.Surjective permutationMap :=
  Assembly.coordinateNumbering.altCongrHom.surjective.comp
    (M22ChapterH.Hexad.innerQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))

theorem permutationMap_coe (g : Inner) :
    (permutationMap g).val = Assembly.sixPointMap (innerToOuter g) := by
  change Assembly.coordinateNumbering.permCongrHom
    (M22ChapterH.Hexad.innerQuotientEquiv (QuotientGroup.mk g)).val = _
  rw [M22ChapterH.Hexad.innerQuotientEquiv_mk]
  rfl

/-- The quotient by the five-space has the literal six-point core action of A6. -/
theorem quotientCore_equivariant (g : Inner) (v : M22Code ⧸ V5.toSubmodule) :
    actionData.quotientCoreEquiv (V5.quotientRepresentation (innerToOuter g) v) =
      BinaryPermutation.coreRepresentation (Fin 6) (permutationMap g).val
        (actionData.quotientCoreEquiv v) :=
  (code_clauses.1.permutation_core (innerToOuter g) v).trans
    (congrArg (fun s : Equiv.Perm (Fin 6) => BinaryPermutation.coreRepresentation (Fin 6) s
      (actionData.quotientCoreEquiv v)) (permutationMap_coe g).symm)

def innerImage : Subgroup MathieuCode.m22PairStabilizer := Inner.map m22ToPairStabilizer

theorem kernel_le_innerImage : Kernel ≤ innerImage := by
  have hi : m22InnerHexadKernel m22SourceOctad ≤ M22ChapterH.Hexad.Action.Inner := Subgroup.map_subtype_le _
  calc
    Kernel = (m22InnerHexadKernel m22SourceOctad).map m22ToPairStabilizer :=
      M22ChapterH.Hexad.inner_kernel_map_pair.symm
    _ ≤ innerImage := Subgroup.map_mono hi

/-- A vector fixed by the inner stabilizer lies in its deleted-six kernel fixed space,
where the surjective A6 action has no nonzero fixed vector. -/
theorem cocode_fixed_eq_bot : fixedSpace m22OuterCocodeRepresentation innerImage = ⊥ := by
  apply bot_unique
  intro v hv
  have hk : v ∈ U.toSubmodule := fun k => hv ⟨k.val, kernel_le_innerImage k.property⟩
  let w : U.toSubmodule := ⟨v, hk⟩
  have hw : actionData.fixedEquiv w = 0 := by
    apply BinaryPermutation.sixDeleted_fixed_eq_zero
    intro s
    obtain ⟨g, rfl⟩ := permutationMap_surjective s
    have hg : U.toRepresentation (innerToOuter g) w = w :=
      Subtype.ext (hv ⟨m22ToPairStabilizer g.val, ⟨g.val, g.property, rfl⟩⟩)
    have he := actionData.fixedEquiv_equivariant (innerToOuter g) w
    exact (congrArg (fun t : Equiv.Perm (Fin 6) =>
      BinaryPermutation.deletedRepresentation (Fin 6) t (actionData.fixedEquiv w))
      (permutationMap_coe g)).trans
      (he.symm.trans (congrArg actionData.fixedEquiv hg))
  have hz : w = 0 := actionData.fixedEquiv.map_eq_zero_iff.mp hw
  exact congrArg Subtype.val hz

/-- The whole native ten-dimensional code is moved by the inner hexad stabilizer. -/
theorem full_movement : subspaceCommutator m22CodeRepresentation ⊤ Inner = ⊤ := by
  change subspaceCommutator (m22OuterCodeRepresentation.comp m22ToPairStabilizer) ⊤ Inner = ⊤
  rw [subspaceCommutator_comp_map, subspaceCommutator_top_eq_coinvariants]
  change codeCommutator innerImage = ⊤
  rw [codeCommutator_eq_annihilator, cocode_fixed_eq_bot,
    Submodule.dualAnnihilator_bot, Submodule.comap_top]

/-- The inner intrinsic kernel moves exactly the same five-space. -/
theorem kernel_movement :
    subspaceCommutator m22CodeRepresentation ⊤ (m22InnerHexadKernel m22SourceOctad) =
      codeCommutator Kernel := by
  change subspaceCommutator (m22OuterCodeRepresentation.comp m22ToPairStabilizer) ⊤ _ = _
  rw [subspaceCommutator_comp_map, M22ChapterH.Hexad.inner_kernel_map_pair,
    subspaceCommutator_top_eq_coinvariants]
  rfl

theorem kernel_movement_finrank : Module.finrank (ZMod 2)
    (subspaceCommutator m22CodeRepresentation ⊤ (m22InnerHexadKernel m22SourceOctad)) = 5 := by
  rw [kernel_movement]
  exact commutator_finrank

/-- The actual inner kernel has the same code fixed line. -/
theorem kernel_fixed :
    fixedSpace m22CodeRepresentation (m22InnerHexadKernel m22SourceOctad) = V1.toSubmodule := by
  change fixedSpace (m22OuterCodeRepresentation.comp m22ToPairStabilizer) _ = _
  rw [fixedSpace_comp_map, M22ChapterH.Hexad.inner_kernel_map_pair]
  rfl

theorem relativeKernel_map :
    ((m22InnerHexadKernel m22SourceOctad).subgroupOf Inner).map innerToOuter =
      Kernel.subgroupOf Stabilizer := by
  apply Subgroup.map_injective Stabilizer.subtype_injective
  rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le kernel_le_stabilizer]
  change ((m22InnerHexadKernel m22SourceOctad).subgroupOf Inner).map
    (m22ToPairStabilizer.comp Inner.subtype) = Kernel
  have hi : m22InnerHexadKernel m22SourceOctad ≤ M22ChapterH.Hexad.Action.Inner := Subgroup.map_subtype_le _
  rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hi]
  exact M22ChapterH.Hexad.inner_kernel_map_pair

/-- In the literal quotient by the fixed line, the inner kernel fixes exactly Vz/Z. -/
theorem fixedQuotient :
    fixedSpace (V1.quotientRepresentation.comp innerToOuter)
        ((m22InnerHexadKernel m22SourceOctad).subgroupOf Inner) = commutatorImage := by
  rw [fixedSpace_comp_map, relativeKernel_map]
  exact code_clauses.2.2.2.2

/-- The action of the native inner kernel on the literal five-space. -/
def kernelAction : m22InnerHexadKernel m22SourceOctad →* BinaryLinear.GL V5.toSubmodule :=
  codeKernelAction.comp kernelToOuter.toMonoidHom

theorem kernelAction_apply (a : m22InnerHexadKernel m22SourceOctad) (v : V5.toSubmodule) :
    (kernelAction a v).val = m22CodeRepresentation a.val v.val := by
  change m22OuterCodeRepresentation (kernelToOuter a).val v.val = _
  rw [kernelToOuter_coe]
  rfl

/-- Restriction retains the complete group of transvections with the actual fixed line. -/
theorem kernelAction_full : kernelAction.range = BinaryLinear.radical codeCenter.toSubmodule := by
  rw [kernelAction, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr kernelToOuter.surjective, ← MonoidHom.range_eq_map]
  exact code_clauses.1.full

end CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeInner
