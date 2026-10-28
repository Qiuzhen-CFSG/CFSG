module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check000
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check001
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check002
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check003
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check004
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check005
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check006
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check007
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check008
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check009
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check010
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check011
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check012
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check013
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check014
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check015
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check016
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check017
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check018
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check019
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check020
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check021
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check022
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check023
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check024
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check025
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check026
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check027
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check028
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check029
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check030
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check031
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check032
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Check033

/-! Kernel replay for a nonstandard binary Ree reflection pair.
Generated from the six sound coset-word rules; see `../source/README.md`. -/

public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid.Case2
open Subgroup.CosetWordCertificate
theorem all_hold {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ) :
    ∀ n, n < 138395 → Holds H g ρ (facts n) := by
  have h0 := advance_0 valid (fun n h => (Nat.not_lt_zero n h).elim)
  have h4096 := advance_4096 valid h0
  have h8192 := advance_8192 valid h4096
  have h12288 := advance_12288 valid h8192
  have h16384 := advance_16384 valid h12288
  have h20480 := advance_20480 valid h16384
  have h24576 := advance_24576 valid h20480
  have h28672 := advance_28672 valid h24576
  have h32768 := advance_32768 valid h28672
  have h36864 := advance_36864 valid h32768
  have h40960 := advance_40960 valid h36864
  have h45056 := advance_45056 valid h40960
  have h49152 := advance_49152 valid h45056
  have h53248 := advance_53248 valid h49152
  have h57344 := advance_57344 valid h53248
  have h61440 := advance_61440 valid h57344
  have h65536 := advance_65536 valid h61440
  have h69632 := advance_69632 valid h65536
  have h73728 := advance_73728 valid h69632
  have h77824 := advance_77824 valid h73728
  have h81920 := advance_81920 valid h77824
  have h86016 := advance_86016 valid h81920
  have h90112 := advance_90112 valid h86016
  have h94208 := advance_94208 valid h90112
  have h98304 := advance_98304 valid h94208
  have h102400 := advance_102400 valid h98304
  have h106496 := advance_106496 valid h102400
  have h110592 := advance_110592 valid h106496
  have h114688 := advance_114688 valid h110592
  have h118784 := advance_118784 valid h114688
  have h122880 := advance_122880 valid h118784
  have h126976 := advance_126976 valid h122880
  have h131072 := advance_131072 valid h126976
  have h135168 := advance_135168 valid h131072
  exact h135168

/-- The wrong braid forces the second reflection into the first endpoint. -/
theorem reflection_mem {G : Type*} [Group G] (g : Nat → G) (H : Subgroup G)
    (hg : ∀ j, j < 4 → g j ∈ H)
    (hr : ∀ i : Fin 39, eval g (relator i) = 1)
    (hb : eval g badWord = 1) : g 4 ∈ H := by
  have valid : Valid context H g (definitions.repr g) := by
    apply definitions.valid
    · intro a ha
      have ha' : a.2 = true ∧ a.1 < 4 := by simpa [allowed] using ha
      simpa [ha'.1] using hg a.1 ha'.2
    · intro i
      unfold relatorWords
      split
      · exact hr _
      · split
        · exact hb
        · simp
  have hh := all_hold valid 138394 (by decide)
  have hs : facts 138394 = ⟨0, [(4,true)], 0⟩ := by decide +kernel
  rw [hs] at hh
  obtain ⟨k,hk⟩ := hh
  have hk' : g 4 = k.val := by simpa using hk
  exact hk'.symm ▸ k.property

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
