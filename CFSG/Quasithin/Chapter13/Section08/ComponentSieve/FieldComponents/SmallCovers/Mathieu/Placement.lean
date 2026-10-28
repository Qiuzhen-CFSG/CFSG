module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.NativeInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.HexadLift
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.SourceGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.QuotientParabolic
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion

/-!
# The subgroup step of the ordinary M₂₂ exclusion

From the genuine standing setup and the earlier nontrivial commutator seed,
`Setup.source_placement` constructs K₁ inside K with the literal quotient
K₁/O₂,Z(K) an E₁₆-by-A₆ extension and J/O₂,Z(K) an ordinary maximal
parabolic. The exact three-part |L₁|₃=3 excludes the covered-A₆ alternative
using its earlier order-nine local quotient (`Setup.source_uncovered`).

The actual radical O₂(K₁T) is contained in T and hence in L₁T by the supplied
Sylow arrangement. Its image through H→H/O₂(H) and the faithful design action
is exactly the hexad pointwise kernel, including when an outer supplement
occurs. The restricted radical homomorphism retains its kernel, range, and
compatibility with the original K/O₂(K) model and component-star map.

One explicit M₂₂ conjugation supplies standard marked coordinates for both
the hexad and its radical. The pair–hexad and three-pair parabolic classes
are distinct and both are retained; the radical in either case is the
standard hexad core, contained in the standard three-pair core. No conclusion
identifies those two parabolic classes. The code-module identification and
terminal contradiction remain with the parent M₂₂ exclusion.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973), together
with the earlier source inputs stated in `Placement.Setup` and the
covered-A₆ local quotient from Notation 13.2.1 and 13.7.5 (printed p.938).
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G}

/-- The proved subgroup-placement outputs, with the source maps retained. -/
structure Witness (s : Setup H K L₁ T G₁ M) where
  hexad : Finset (Fin 22)
  hexad_mem : hexad ∈ m22Blocks
  conjugator : M22
  hexad_eq : hexad = conjugator • m22Hexad123
  native_parabolic :
    markedImage K (K ⊓ M) s.model =
      M22SolvableSylow.pairHexad.map (MulAut.conj conjugator).toMonoidHom ∨
    markedImage K (K ⊓ M) s.model =
      M22ValueBound.Concrete.second.map (MulAut.conj conjugator).toMonoidHom
  denominator_le_overlap : (centralPreimage (pCore 2 K)).map K.subtype ≤ K ⊓ M
  overlap_le_lift : K ⊓ M ≤ hexadLift K s.model hexad
  parabolic : IsCoatom (overlapInLiftQuotient K M s.model hexad)
  extension : AlternatingBySixteen (hexadLift K s.model hexad ⧸
    (centralPreimage (pCore 2 K)).comap (inclusion (hexadLift_le K s.model hexad))) 6
  three_part : 3 ^ (Nat.card L₁).factorization 3 = 3
  sylow_stabilizes : (Source.starImage H T).map s.designHom ≤
    MulAction.stabilizer m22DesignAut hexad
  radical_le : ((hexadLift K s.model hexad ⊔ T).subgroupOf H).pCoreIn 2 ≤
    (L₁ ⊔ T).subgroupOf H
  radical_image : ((s.hexadOvergroup hexad).pCoreIn 2).map s.starDesignMap =
    (m22HexadPointwiseKernel hexad).map M22ValueBound.Concrete.inclusion
  radicalMap : (s.hexadOvergroup hexad).pCoreIn 2 →* M22
  radical_range : radicalMap.range = m22HexadPointwiseKernel hexad
  radical_ker : radicalMap.ker =
    (pCore 2 H).subgroupOf ((s.hexadOvergroup hexad).pCoreIn 2)
  radical_design : ∀ x, M22ValueBound.Concrete.inclusion (radicalMap x) = s.starDesignMap x.val
  radical_component : ∀ (x : (s.hexadOvergroup hexad).pCoreIn 2) (k : K),
    x.val.val = k.val → radicalMap x = componentMap K s.model k

namespace Setup
variable (s : Setup H K L₁ T G₁ M)
include s

/-- The subgroup paragraph of the ordinary M₂₂ branch, from the actual earlier
source inputs and the nontrivial commutator seed. No placement is assumed. -/
theorem source_placement (V₃ : Subgroup G) (hne : V₃ ≠ ⊥)
    (hgen : ⁅V₃, L₁⁆ = V₃) : Nonempty (Witness s) := by
  obtain ⟨B, hB, hX, hmax, hk, hc, hT⟩ := s.exists_native_placement V₃ hne hgen
  obtain ⟨g, hBg, hg⟩ := s.marked_conjugacy hB hX hk hc
  obtain ⟨f, hf, hfker, hfdesign, hfcomponent⟩ := s.exists_hexadRadicalMap hB hT
  exact ⟨{
    hexad := B
    hexad_mem := hB
    conjugator := g
    hexad_eq := hBg
    native_parabolic := hg
    denominator_le_overlap := by
      rw [centralPreimageIn_eq_twoCoreIn K s.model]
      exact s.component_core_le_overlap
    overlap_le_lift := s.overlap_le_hexadLift hX
    parabolic := overlapInLiftQuotient_isCoatom K M s.model B hmax
    extension := hexadLiftQuotient_extension K s.model hB
    three_part := s.three_part_of_overlap_card V₃ hne hgen hc
    sylow_stabilizes := hT
    radical_le := (s.radical_le_sylow _).trans (comap_mono le_sup_right)
    radical_image := s.hexadRadical_image hB hT
    radicalMap := f
    radical_range := hf
    radical_ker := hfker
    radical_design := hfdesign
    radical_component := hfcomponent }⟩

/-- The earlier order-nine quotient in the covered alternative is incompatible
with the placement's exact three-part. -/
theorem source_uncovered (V₃ L : Subgroup G) (hne : V₃ ≠ ⊥)
    (hgen : ⁅V₃, L₁⁆ = V₃)
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hcovered : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 9) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨w⟩ := s.source_placement V₃ hne hgen
  exact uncovered_of_three_part L L₁ w.three_part hmodels hcovered

end Setup
namespace Witness
variable {s : Setup H K L₁ T G₁ M} (w : Witness s)

/-- The seed lies in the same actual K₁ used by the radical map. -/
theorem seed_le_lift : L₁ ≤ hexadLift K s.model w.hexad :=
  s.seed_le_overlap.trans w.overlap_le_lift

/-- All component coordinates change by the specified native conjugation. -/
noncomputable def markedModel : (K ⧸ pCore 2 K) ≃* M22 :=
  s.model.trans (MulAut.conj w.conjugator).symm

/-- Every native subgroup image changes by the same specified conjugation. -/
theorem markedImage_eq (X : Subgroup G) :
    markedImage K X w.markedModel =
      (markedImage K X s.model).map (MulAut.conj w.conjugator).symm.toMonoidHom := by
  rw [markedImage, markedImage, map_map]
  rfl

/-- The source overlap in the normalized component model retains both classes. -/
theorem marked_overlap :
    markedImage K (K ⊓ M) w.markedModel = M22SolvableSylow.pairHexad ∨
      markedImage K (K ⊓ M) w.markedModel = M22ValueBound.Concrete.second := by
  rw [w.markedImage_eq]
  rcases w.native_parabolic with h | h
  · left
    rw [h]
    exact (MulAut.conj w.conjugator).mapSubgroup.symm_apply_apply _
  · right
    rw [h]
    exact (MulAut.conj w.conjugator).mapSubgroup.symm_apply_apply _

/-- The actual chosen K₁ becomes the standard hexad stabilizer in that model. -/
theorem marked_lift :
    markedImage K (hexadLift K s.model w.hexad) w.markedModel =
      MulAction.stabilizer M22 m22Hexad123 := by
  rw [w.markedImage_eq, hexadLift_image, w.hexad_eq,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact (MulAut.conj w.conjugator).mapSubgroup.symm_apply_apply _

/-- The radical map expressed in the standard marked hexad coordinates. -/
noncomputable def markedRadicalMap : (s.hexadOvergroup w.hexad).pCoreIn 2 →* M22 :=
  (MulAut.conj w.conjugator).symm.toMonoidHom.comp w.radicalMap

/-- The normalized radical is exactly the standard hexad translation group. -/
theorem markedRadicalMap_range : w.markedRadicalMap.range =
    m22HexadPointwiseKernel m22Hexad123 := by
  rw [markedRadicalMap, MonoidHom.range_comp, w.radical_range,
    w.hexad_eq, m22HexadPointwiseKernel_smul]
  exact (MulAut.conj w.conjugator).mapSubgroup.symm_apply_apply _

/-- Thus the marked radical is the genuine native hexad core. -/
theorem markedRadicalMap_range_eq_core : w.markedRadicalMap.range =
    (MulAction.stabilizer M22 m22Hexad123).pCoreIn 2 := by
  rw [w.markedRadicalMap_range, Native.hexad_core_eq_kernel]

/-- Both parabolic classes have compatible hexad/three-pair radical coordinates;
this does not identify the pair–hexad class with the three-pair class. -/
theorem markedRadicalMap_range_le_partition_core : w.markedRadicalMap.range ≤
    M22ValueBound.Concrete.second.pCoreIn 2 := by
  rw [w.markedRadicalMap_range_eq_core]
  exact Native.native_core_le_partition_core

/-- Compatibility keeps the actual design action after coordinate normalization. -/
theorem markedRadicalMap_design (x : (s.hexadOvergroup w.hexad).pCoreIn 2) :
    M22ValueBound.Concrete.inclusion
      ((MulAut.conj w.conjugator) (w.markedRadicalMap x)) = s.starDesignMap x.val := by
  simpa only [markedRadicalMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] using w.radical_design x

/-- The same conjugation normalizes the original K/O₂(K) coordinates. -/
theorem markedRadicalMap_component (x : (s.hexadOvergroup w.hexad).pCoreIn 2)
    (k : K) (hxk : x.val.val = k.val) :
    w.markedRadicalMap x = componentMap K w.markedModel k := by
  change (MulAut.conj w.conjugator).symm (w.radicalMap x) = _
  rw [w.radical_component x k hxk]
  rfl

end Witness
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
