module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.AmbientCentralizers
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PrimedQuotientCentralizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.NativeObstruction

/-!
# Ambient centralizer of the literal signed primed row

The native seed, the two (d') word lifts, and the signed Figure 1 pair lift
lie in the second constructed elementary eight. Their quotient centralizer
is the full unprimed (d) row, and their kernel fixed subgroup is unchanged.
Removing a lift from the constructed eight proves equality of the entire
ambient centralizer with that eight. The statement retains the specified
signed lift; source-wide marking and fusion are separate calculations.
Source: Kleidman--Wilson (1988), Proposition 2.3.5, Case (iii).
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Cardinality KernelCount QuotientCount.Image SylowCore SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "L" => SylowCore.Local
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four
local notation "e" => maskEquiv matrixA_mul_self matrixB_pow_four

def primedNativeGenerator : Fin 4 → L :=
  ![nativeMask 1, correctedLift 3, correctedLift 4, twistedPairLift]

def primedLocalRow : Subgroup L := closure (Set.range primedNativeGenerator)

def primedNativeRow : Subgroup Model := primedLocalRow.map (L).subtype

theorem primedLocalRow_le_localEight : primedLocalRow ≤ localEight 1 := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  fin_cases j
  · exact kernelPair_mem_localEight 1 0
  · exact correctedGenerator_mem_localEight 1 1
  · exact correctedGenerator_mem_localEight 1 2
  · exact (localEight 1).mul_mem (kernelPair_mem_localEight 1 1)
      (correctedGenerator_mem_localEight 1 3)

instance primedLocalRow_elementary : IsElementaryAbelian 2 primedLocalRow := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro a b
    apply Subtype.ext
    exact setLike_mul_comm (primedLocalRow_le_localEight a.property)
      (primedLocalRow_le_localEight b.property)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : L)
      (primedLocalRow_le_localEight a.property)

instance primedNativeRow_elementary : IsElementaryAbelian 2 primedNativeRow :=
  IsElementaryAbelian.map_subtype

theorem primedLocalRow_projection : primedLocalRow.map π = pairRowImage 3 := by
  rw [primedLocalRow, MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext j
  fin_cases j
  · exact nativeMask_projection 1
  · exact correctedLift_projection 3
  · exact correctedLift_projection 4
  · change π (nativeMask 4 * correctedLift 5) = pairPermutation
    rw [map_mul, nativeMask_projection, correctedLift_projection, one_mul]
    rfl

private theorem primed_kernel_centralizer :
    ((centralizer (primedLocalRow : Set L)).subgroupOf E).map (E).subtype = centralKernel 1 := by
  unfold centralKernel
  congr 1
  ext x
  obtain ⟨m,rfl⟩ := (e).surjective x
  change (e m : L) ∈ centralizer (primedLocalRow : Set L) ↔
    (e m : L) ∈ centralizer (liftClosure 1 : Set L)
  rw [mask_mem_pairRow_centralizer_iff _ _ primedLocalRow_projection,
    mask_mem_pairRow_centralizer_iff _ _ (liftClosure_projection 1)]
  rfl

theorem primedLocalRow_centralizer :
    centralizer (primedLocalRow : Set L) = localEight 1 := by
  have hle : localEight 1 ≤ centralizer (primedLocalRow : Set L) :=
    (localEight 1).le_centralizer.trans (centralizer_le primedLocalRow_le_localEight)
  apply le_antisymm ?_ hle
  intro g hg
  have hp : π g ∈ pairRowImage 1 := by
    rw [← primed_d_quotient_centralizer]
    intro p hp
    rw [← primedLocalRow_projection] at hp
    obtain ⟨a,ha,rfl⟩ := hp
    exact (map_mul π a g).symm.trans ((congrArg π (hg a ha)).trans (map_mul π g a))
  change π g ∈ pairRowImage ((1 : Fin 2).castLE (by decide)) at hp
  rw [← liftClosure_projection 1] at hp
  obtain ⟨a,ha,he⟩ := hp
  have ha8 : a ∈ localEight 1 := (show liftClosure 1 ≤ localEight 1 from le_sup_left) ha
  have hk : g * a⁻¹ ∈ E := by
    rw [← starProjection_ker, MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hc : g * a⁻¹ ∈ centralizer (primedLocalRow : Set L) :=
    (centralizer _).mul_mem hg ((centralizer _).inv_mem (hle ha8))
  have hm : g * a⁻¹ ∈ centralKernel 1 := by
    rw [← primed_kernel_centralizer]
    exact ⟨⟨g * a⁻¹,hk⟩,hc,rfl⟩
  have hh := (localEight 1).mul_mem ((show centralKernel 1 ≤ localEight 1 from le_sup_right) hm) ha8
  simpa only [inv_mul_cancel_right] using hh

theorem seed_mem_primedNativeRow :
    (InvolutionCentralizers.Second.seed : Model) ∈ primedNativeRow := by
  have hs : nativeMask 1 = InvolutionCentralizers.Second.seed :=
    Simplicity.Max1Fusion.KernelOrbits.maskValue_one matrixA_mul_self matrixB_pow_four
  rw [← hs]
  exact mem_map_of_mem (L).subtype (subset_closure (Set.mem_range_self 0))

/-- The complete ambient centralizer of the specified signed primed row is
exactly the second native elementary eight. -/
theorem primedNativeRow_centralizer :
    centralizer (primedNativeRow : Set Model) = nativeEight 1 := by
  rw [seed_ambient_centralizer_map primedNativeRow (map_subtype_le _) seed_mem_primedNativeRow]
  have he : primedNativeRow.subgroupOf L = primedLocalRow :=
    comap_map_eq_self_of_injective (L).subtype_injective _
  rw [he, primedLocalRow_centralizer]
  rfl

end Janko4.LocalStructure.ElementaryEightGeometry
