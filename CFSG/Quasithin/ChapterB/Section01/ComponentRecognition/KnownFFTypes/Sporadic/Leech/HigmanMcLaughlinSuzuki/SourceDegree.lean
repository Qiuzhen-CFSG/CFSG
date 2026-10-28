module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.Inputs
public import Theory.Representation.EndFieldDegree
public import Theory.Representation.EndFieldFrobenius
public import Theory.Representation.NormalPSubgroupKernel

/-!
# Descent of the Higman--Sims degree window to the binary field

An irreducible binary module becomes absolutely irreducible over its actual
commuting endomorphism field. If its absolute degree in the window at most
fifty is twenty, its binary degree is twenty or forty. To eliminate forty it
suffices to prove that the degree-twenty traces satisfy `t² = t`: the traces
span the commuting field, so that field has degree one over the binary field.

The source application first removes a two-group center by the normal
p-subgroup kernel theorem, then transports the literal action on the same
binary vector space through the given HS central-quotient isomorphism.

The two concrete representation inputs and the two-group center bound remain
explicit. In particular this module does not assert the unconditional HS
recognition or the Chapter K exclusion. The existing J2/HS multiplier owner
supplies the center bound; separate character calculations supply the degree
window and trace condition. No cubic-ratio hypothesis is used for descent.

Source: Guralnick--Malle, *Classification of 2F-modules, I*, Proposition 5.1,
HS paragraph (author preprint, p.16), citing the Brauer character and
low-dimensional representation tables; Aschbacher--Smith K.4, printed p.457.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MonoidAlgebra

universe u v

section BinaryDescent
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) KnownSimple.SporadicName.hs.Carrier V)
  [σ.IsIrreducible] [IsSimpleGroup KnownSimple.SporadicName.hs.Carrier]

/-- Absolute degree twenty alone leaves precisely two possible binary degrees
in the required window. This records the field-of-definition issue explicitly. -/
theorem finrank_eq_twenty_or_forty_of_absolute_window
    (hf : Function.Injective σ) (hdegree : AbsoluteDegreeWindow.{v})
    (hd : Module.finrank (ZMod 2) V ≤ 50) :
    Module.finrank (ZMod 2) V = 20 ∨ Module.finrank (ZMod 2) V = 40 := by
  let E := Module.End (ZMod 2)[KnownSimple.SporadicName.hs.Carrier] σ.asModule
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  have ha : Module.finrank E σ.asModule = 20 :=
    hdegree inferInstance E σ.asModule σ.endFieldRep ((endFieldRep_injective_iff σ).mpr hf)
      (endFieldRep_isAbsolutelyIrreducible σ) ((endField_finrank_le σ).trans hd)
  have ht := finrank_eq_endField_mul σ
  have hp := schurDegree_pos 2 σ
  change 0 < Module.finrank (ZMod 2) E at hp
  rw [ha] at ht
  dsimp only [E] at hp
  omega

/-- Frobenius-fixed traces force the actual commuting field to be binary;
therefore the absolute degree equals the original binary degree. -/
theorem finrank_eq_twenty_of_absolute_window_of_trace
    (hf : Function.Injective σ) (hdegree : AbsoluteDegreeWindow.{v})
    (htrace : DegreeTwentyTraceField.{v})
    (hd : Module.finrank (ZMod 2) V ≤ 50) : Module.finrank (ZMod 2) V = 20 := by
  let E := Module.End (ZMod 2)[KnownSimple.SporadicName.hs.Carrier] σ.asModule
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  have hfE := (endFieldRep_injective_iff σ).mpr hf
  have hiE := endFieldRep_isAbsolutelyIrreducible σ
  have ha : Module.finrank E σ.asModule = 20 :=
    hdegree inferInstance E σ.asModule σ.endFieldRep hfE hiE ((endField_finrank_le σ).trans hd)
  have ht := htrace inferInstance E σ.asModule σ.endFieldRep hfE hiE ha
  have hdiv : schurDegree 2 σ ∣ 1 :=
    (endFieldRep_trace_frobenius_iff 2 σ 1).mp (by simpa using ht)
  have hE : Module.finrank (ZMod 2) E = 1 := Nat.dvd_one.mp hdiv
  rw [finrank_eq_endField_mul σ, hE, ha, one_mul]

end BinaryDescent

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The actual source central quotient supplies simplicity of the fixed HS
carrier, without an independent order or simplicity certification. -/
theorem SourceHypotheses.carrier_isSimpleGroup (h : SourceHypotheses ρ) :
    IsSimpleGroup KnownSimple.SporadicName.hs.Carrier := by
  let := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    IsQuasisimple.simple
  obtain ⟨e⟩ := h.centralQuotient
  exact e.symm.isSimpleGroup

/-- A two-group center of the source cover acts trivially on the irreducible
restriction. Faithfulness removes that center. The multiplier input is explicit. -/
theorem SourceHypotheses.center_eq_bot_of_two_group (h : SourceHypotheses ρ)
    (hcenter : IsPGroup 2 (center (generalizedFitting G))) :
    center (generalizedFitting G) = ⊥ := by
  let σ : Representation (ZMod 2) (generalizedFitting G) V :=
    ρ.comp (generalizedFitting G).subtype
  let : σ.IsIrreducible := h.irreducible
  have hf : Function.Injective σ :=
    h.faithful.comp (generalizedFitting G).subtype_injective
  have hk := normal_p_subgroup_le_ker σ (center (generalizedFitting G)) hcenter
  rw [(σ.ker_eq_bot_iff).mpr hf] at hk
  exact le_bot_iff.mp hk

/-- Remove the source center and transport to the actual HS carrier, keeping
the original binary vector space and faithful irreducible action. -/
theorem SourceHypotheses.exists_carrier_representation_of_two_group_center
    (h : SourceHypotheses ρ)
    (hcenter : IsPGroup 2 (center (generalizedFitting G))) :
    ∃ σ : Representation (ZMod 2) KnownSimple.SporadicName.hs.Carrier V,
      Function.Injective σ ∧ σ.IsIrreducible := by
  obtain ⟨e⟩ := h.centralQuotient
  let q : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃*
      generalizedFitting G :=
    (QuotientGroup.quotientMulEquivOfEq (h.center_eq_bot_of_two_group hcenter)).trans
      QuotientGroup.quotientBot
  let f := q.symm.trans e
  let τ := ρ.comp (generalizedFitting G).subtype
  let σ := τ.comp f.symm.toMonoidHom
  refine ⟨σ, (h.faithful.comp (generalizedFitting G).subtype_injective).comp
    f.symm.injective, ?_⟩
  exact (irreducible_comp_surjective_iff f.symm.toMonoidHom f.symm.surjective τ).mpr
    h.irreducible

/-- Source degree recognition after discharging the three independent inputs:
the HS cover-center bound, absolute degree window, and degree-twenty traces. -/
theorem SourceHypotheses.finrank_eq_twenty_of_representation_inputs
    (h : SourceHypotheses ρ)
    (hcenter : IsPGroup 2 (center (generalizedFitting G)))
    (hdegree : AbsoluteDegreeWindow.{v}) (htrace : DegreeTwentyTraceField.{v})
    (hd : Module.finrank (ZMod 2) V ≤ 50) : Module.finrank (ZMod 2) V = 20 := by
  obtain ⟨σ, hf, hi⟩ := h.exists_carrier_representation_of_two_group_center hcenter
  let := hi
  let := h.carrier_isSimpleGroup
  exact finrank_eq_twenty_of_absolute_window_of_trace σ hf hdegree htrace hd

/-- Application to the literal Chapter K consumer. This leaves the model
inputs explicit and is not an unconditional exclusion theorem. -/
theorem SourceHypotheses.not_cubicRatio_le_two_of_representation_inputs
    (h : SourceHypotheses ρ)
    (hcenter : IsPGroup 2 (center (generalizedFitting G)))
    (hdegree : AbsoluteDegreeWindow.{v}) (htrace : DegreeTwentyTraceField.{v})
    (hgen : InvolutionConjugateGenerationBound (generalizedFitting G) 5)
    (hlocal : Module.finrank (ZMod 2) V = 20 →
      ∀ A : Subgroup G, IsElementaryTwo A → 2 * rank A < fixedCodim ρ A) :
    ¬ cubicRatio ρ ≤ 2 := by
  exact h.not_cubicRatio_le_two_of_inputs hgen
    (h.finrank_eq_twenty_of_representation_inputs hcenter hdegree htrace) hlocal

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
