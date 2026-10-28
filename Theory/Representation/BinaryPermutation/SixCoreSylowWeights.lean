module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowFixedLine
public import Theory.Representation.BinaryPermutation.SixCoreOrbits
/-!
# Sylow-fixed vectors in the six-letter augmentation core

The natural quotient has one Sylow-fixed line. Thus every Sylow-fixed
core vector projects either to zero or to the image of a prescribed
nonconstant fixed vector. Each fiber consists of complementary words,
whose weights differ, so a weight determines the fixed vector uniquely.

The finite checks concern only the 32 core vectors, not the actor group.
The original first-parabolic application is in Chapter13 Section04,
FixedCoreSource/Solvable/LocalProduct/FirstFlagNormalizer.
Source: Aschbacher–Smith 13.2.1 and 13.3.4, pp.877 and885.
-/

public section
open Subgroup BinaryPermutation
namespace BinaryPermutation
local instance sixCoreSylowWeightsDecidable : DecidablePred (· ∈ core (Fin 6)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance sixCoreSylowWeightsFintype : Fintype (core (Fin 6)) := Subtype.fintype _
private theorem coreToNatural_ker (v : core (Fin 6)) :
    coreToNatural (Fin 6) v = 0 ↔ v.val ∈ constants (Fin 6) := by
  rw [← Subtype.val_inj]
  exact Submodule.Quotient.mk_eq_zero _
private theorem core_fiber_weight (v w : core (Fin 6))
    (h : coreToNatural (Fin 6) v = coreToNatural (Fin 6) w)
    (hw : wordWeight v.val = wordWeight w.val) : v = w := by
  have hd : v.val - w.val ∈ constants (Fin 6) :=
    (Submodule.Quotient.eq _).mp (congrArg Subtype.val h)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hd
  have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hb c with rfl | rfl
  · apply Subtype.ext
    simpa only [zero_smul, eq_comm, sub_eq_zero] using hc
  · have he : v = w + sixCoreConstant := by
      apply Subtype.ext
      change v.val = w.val + allOne (Fin 6)
      simpa only [one_smul, sub_eq_iff_eq_add, add_comm] using hc.symm
    have hne : ∀ w : core (Fin 6),
        wordWeight (w + sixCoreConstant).val ≠ wordWeight w.val := by
      decide +kernel
    exact (hne w (he ▸ hw)).elim

theorem core_sylow_fixed_quotient_or (P : Sylow 2 (alternatingGroup (Fin 6)))
    (v w : core (Fin 6))
    (hv : coreToNatural (Fin 6) v ≠ 0)
    (hvP : ∀ a ∈ (P : Subgroup (alternatingGroup (Fin 6))),
      alternatingCoreRepresentation (Fin 6) a v = v)
    (hwP : ∀ a ∈ (P : Subgroup (alternatingGroup (Fin 6))),
      alternatingCoreRepresentation (Fin 6) a w = w)
    : coreToNatural (Fin 6) w = 0 ∨
      coreToNatural (Fin 6) w = coreToNatural (Fin 6) v := by
  have hf (u : core (Fin 6))
      (hu : ∀ a ∈ (P : Subgroup (alternatingGroup (Fin 6))),
        alternatingCoreRepresentation (Fin 6) a u = u) :
      ∀ a ∈ (P : Subgroup (alternatingGroup (Fin 6))).map (alternatingGroup (Fin 6)).subtype,
        naturalRepresentation (Fin 6) a (coreToNatural (Fin 6) u) = coreToNatural (Fin 6) u := by
    rintro a ⟨b,hb,rfl⟩
    rw [← coreToNatural_equivariant]
    exact congrArg (coreToNatural (Fin 6)) (hu b hb)
  have hs := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.fixed_vectors_le_span
    (alternatingGroup (Fin 6)) le_rfl P (coreToNatural (Fin 6) v) hv
    (hf v hvP) (coreToNatural (Fin 6) w) (hf w hwP)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hs
  have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hb c with rfl | rfl
  · exact Or.inl (by simpa using hc.symm)
  · exact Or.inr (by simpa using hc.symm)

theorem core_sylow_fixed_eq_of_weight (P : Sylow 2 (alternatingGroup (Fin 6)))
    (v w : core (Fin 6))
    (hv : coreToNatural (Fin 6) v ≠ 0)
    (hvP : ∀ a ∈ (P : Subgroup (alternatingGroup (Fin 6))),
      alternatingCoreRepresentation (Fin 6) a v = v)
    (hwP : ∀ a ∈ (P : Subgroup (alternatingGroup (Fin 6))),
      alternatingCoreRepresentation (Fin 6) a w = w)
    (hweight : wordWeight v.val = wordWeight w.val) : w = v := by
  rcases core_sylow_fixed_quotient_or P v w hv hvP hwP with hw0 | hwe
  · have hconst := (coreToNatural_ker w).mp hw0
    have hcases := (sixCore_fixed_iff w).mp
      ((core_fixed_iff_constant (by simp) w).mpr hconst)
    have hn : ∀ v w : core (Fin 6), (w = 0 ∨ w = sixCoreConstant) →
        wordWeight v.val = wordWeight w.val → v = w := by
      decide +kernel
    exact (hv ((hn v w hcases hweight) ▸ hw0)).elim
  · exact core_fiber_weight w v hwe hweight.symm

end BinaryPermutation
