module

public import Theory.Representation.HexacodeAction.WeightFourVectorCore
public import Theory.Representation.HexacodeAction.FullWeightFourVectorStabilizer
import Theory.GroupTheory.PCoreImage
import Theory.GroupTheory.SylowKernelCore
import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation

/-!
# The fixed line of the full weight-four two-core

The even core fixes precisely the scalar point. The full core contains
an odd field involution, so its fixed vectors in that scalar point are
exactly the original binary line. No coordinate relabeling changes v.

Source: Aschbacher--Smith, proof following12.7.20, printed p.846.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender Theory.SpecificGroups.SymmetricSix DuadCalculation

/-- The full weight-four stabilizer core fixes exactly the original binary line. -/
theorem weightFourFullCore_fixed (v : hexacode) (hv : hammingNorm v.val = 4) :
    fixedSpace action ((fullVectorStabilizer v).pCoreIn 2) =
      Submodule.span Bit {v} := by
  let S := fullVectorStabilizer v
  let E := (fullWeightVectorStabilizer v).map hexSign.ker.subtype
  have hES : E = S ⊓ hexSign.ker := by
    ext g
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨he, e.property⟩
    · rintro ⟨hg, he⟩
      exact ⟨⟨g, he⟩, hg, rfl⟩
  have hSn : S ≤ normalizer (E : Set HexAutomorphisms) := by
    rw [hES]
    exact (le_inf S.le_normalizer (by rw [normalizer_eq_top]; exact le_top)).trans
      inf_normalizer_le_normalizer_inf
  have hcore : ((fullWeightVectorStabilizer v).pCoreIn 2).map hexSign.ker.subtype ≤
      S.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ hexSign.ker.subtype_injective]
    exact pCoreIn_mono_of_normalizes (hES.le.trans inf_le_left) hSn
  obtain ⟨e, _, _, heven⟩ := fullWeightFourVectorStabilizer_model v hv
  have hecore : (pCore 2 S).map e.toMonoidHom = productCore :=
    (pCore_map_iso 2 e).trans productCore_eq.symm
  have hs : (Equiv.swap 0 1, 1) ∈ (pCore 2 S).map e.toMonoidHom := by
    rw [hecore]
    exact ⟨mem_top _, one_mem _⟩
  obtain ⟨g, hg, hgmark⟩ := hs
  have hodd : hexSign g.val = -1 := by
    rcases Int.units_eq_one_or (hexSign g.val) with hh | hh
    · have ht := (heven g).mp hh
      rw [show e g = (Equiv.swap 0 1, 1) from hgmark] at ht
      exact ((by decide : (Equiv.swap 0 1 : Two) ≠ signPermTwo 1) ht).elim
    · exact hh
  have hv0 : v ≠ 0 := by intro hh; simp [hh] at hv
  apply le_antisymm
  · intro w hw
    have hwe : w ∈ fixedSpace evenAction ((fullWeightVectorStabilizer v).pCoreIn 2) := by
      intro b
      exact hw ⟨b.val.val, hcore (mem_map_of_mem _ b.property)⟩
    rw [weightFourVectorCore_fixed v hv] at hwe
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hwe
    have hfixed := hw ⟨g.val, mem_map_of_mem S.subtype hg⟩
    change action g.val (r • v) = r • v at hfixed
    rw [action_odd_smul g.val hodd, show action g.val v = v from g.property] at hfixed
    have hr : SL2FourNatural.fieldFrobenius r = r := (smul_left_injective _ hv0) hfixed
    rcases (SL2FourNatural.fieldFrobenius_fixed r).mp hr with hr | hr
    · simp [hr]
    · rw [hr, one_smul]
      exact Submodule.mem_span_singleton_self (R := Bit) (M := hexacode) v
  · apply Submodule.span_le.mpr
    rintro w (rfl : w = v)
    intro g
    exact pCoreIn_le 2 S g.property

end Representation.Hexacode
