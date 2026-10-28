module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.Actions
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Structure
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes

/-!
# Word core and a distinguished third element in the Held local kernel

The word core is exactly the existing normal two-subgroup, transported from
indices 0 and 1 to the Bool-indexed literal locals. The distinguished element
has cube one and lies in the actual native six-point action kernel. Their join
is a subgroup of that kernel; the reverse containment is a separate certificate.
All normality remains relative to the local overgroup.

Sources: GLS3 Table 5.3p; unchanged ATLAS max3/max4 and degree-2058 data;
quasithin printed pp.509–511 and 747–748, via the retained Held calculation.
-/

public section
set_option maxRecDepth 8192
open Subgroup
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
open Held.TwoLocalCandidates

@[expose] def coreGenerator (i : Bool) (k : Fin 7) : localOvergroup i :=
  match i with
  | false => Cores.coreGenerator 0 k
  | true => Cores.coreGenerator 1 k

@[expose] def wordCore (i : Bool) : Subgroup (localOvergroup i) :=
  match i with
  | false => Cores.core 0
  | true => Cores.core 1

theorem wordCore_eq_closure (i : Bool) :
    wordCore i = closure (Set.range (coreGenerator i)) := by cases i <;> rfl

theorem wordCore_normal (i : Bool) : (wordCore i).Normal := by
  cases i
  · exact Cores.core_normal 0
  · exact Cores.core_normal 1

theorem wordCore_isPGroup (i : Bool) : IsPGroup 2 (wordCore i) := by
  cases i
  · exact Cores.core_isPGroup 0
  · exact Cores.core_isPGroup 1

theorem coreGenerator_mem (i : Bool) (k : Fin 7) : coreGenerator i k ∈ wordCore i := by
  rw [wordCore_eq_closure]
  exact subset_closure (Set.mem_range_self k)

@[expose] def ambientWordCore (i : Bool) : Subgroup Held.He :=
  (wordCore i).map (localOvergroup i).subtype

theorem ambientWordCore_eq_closure (i : Bool) :
    ambientWordCore i = closure (Set.range (fun k => (coreGenerator i k).val)) := by
  rw [ambientWordCore, wordCore_eq_closure, MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem ambientWordCore_le_localTwoCore (i : Bool) : ambientWordCore i ≤ localTwoCore i :=
  map_mono (le_sSup ⟨wordCore_normal i, wordCore_isPGroup i⟩)

theorem localOvergroup_le_normalizer_ambientWordCore (i : Bool) :
    localOvergroup i ≤ normalizer (ambientWordCore i : Set Held.He) := by
  apply le_normalizer_iff.mpr
  rintro g hg x ⟨y, hy, rfl⟩
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, (wordCore_normal i).conj_mem y hy ⟨g, hg⟩, rfl⟩

@[expose] def oddGenerator (i : Bool) (j k : Fin 2) : localOvergroup i :=
  wordElement i (LocalActions.oddWord i j k)

@[expose] def twoGenerator (i : Bool) (j : Fin 2) (k : Fin 4) : localOvergroup i :=
  wordElement i (LocalActions.twoWord i j k)

@[expose] def kernelThird (i : Bool) : localOvergroup i :=
  if i then oddGenerator i 0 0 * oddGenerator i 0 1 else oddGenerator i 0 0

theorem oddGenerator_val (i : Bool) (j k : Fin 2) :
    (oddGenerator i j k).val = LocalActions.RepresentativeImages.oddGenerator i j k := rfl

theorem kernelThird_cube (i : Bool) : kernelThird i ^ 3 = 1 := by
  apply Subtype.val_injective
  simp only [Subgroup.coe_pow, Subgroup.coe_one, kernelThird]
  cases i
  · exact LocalActions.RepresentativeImages.oddGenerator_cube false 0 0
  · simp only [↓reduceIte, Subgroup.coe_mul, oddGenerator_val]
    rw [(LocalActions.RepresentativeImages.oddGenerator_commute true 0).mul_pow,
      LocalActions.RepresentativeImages.oddGenerator_cube,
      LocalActions.RepresentativeImages.oddGenerator_cube, mul_one]

theorem kernelThird_mem_ker (i : Bool) : kernelThird i ∈ (SixPoint.action i).ker := by
  have h (k : Fin 2) : SixPoint.action i (oddGenerator i 0 k) = imageGenerator i 0 ⟨k.val, by omega⟩ :=
    action_oddWord i 0 k
  change SixPoint.action i (kernelThird i) = 1
  cases i
  · change SixPoint.action false (oddGenerator false 0 0) = 1
    rw [h]
    decide +kernel
  · change SixPoint.action true (oddGenerator true 0 0 * oddGenerator true 0 1) = 1
    rw [map_mul, h, h]
    decide +kernel

@[expose] def kernelEnvelope (i : Bool) : Subgroup (localOvergroup i) :=
  wordCore i ⊔ zpowers (kernelThird i)

theorem kernelEnvelope_le_ker (i : Bool) : kernelEnvelope i ≤ (SixPoint.action i).ker :=
  by
  have hC : wordCore i ≤ pCore 2 (localOvergroup i) :=
    le_sSup ⟨wordCore_normal i, wordCore_isPGroup i⟩
  exact sup_le (hC.trans (SixPoint.twoCore_le_ker_action i))
    (zpowers_le.mpr (kernelThird_mem_ker i))
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
