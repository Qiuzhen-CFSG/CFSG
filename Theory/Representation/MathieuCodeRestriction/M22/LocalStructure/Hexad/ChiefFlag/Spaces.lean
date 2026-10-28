module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Duality

/-!
# The actual hexad code spaces and quotient actions

The intrinsic two-core is normal inside the hexad stabilizer. Consequently
its code and cocode fixed spaces and the code commutator carry the literal
stabilizer actions. Orbit counting for this two-group gives a nonzero fixed
vector in the commutator; the fixed line is therefore contained in it. The
known dimensions prove the strict prefix 0 < V1 < V5 < V. Coordinate duality
also transfers the earlier displacement four to code fixed dimension six.

The quotient fixed space and the image of the commutator are defined
independently. Their equality, the rank-six flag term, chief-factor
irreducibility and the remaining action identifications are not asserted.

Source: Aschbacher--Smith, H.16.4, printed p.403, combined manuscript of
1 March 2004. Earlier M24 fixed-space and H.14 kernel data remain explicit.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
namespace MathieuCode.Hexad.ChiefFlag

abbrev Stabilizer := m22OuterHexadStabilizer m22SourceOctad
abbrev Kernel := m22OuterHexadKernel m22SourceOctad

theorem kernel_le_stabilizer : Kernel ≤ Stabilizer := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

theorem stabilizer_le_normalizer : Stabilizer ≤ Subgroup.normalizer (Kernel : Set m22PairStabilizer) := by
  have h := (pCore 2 Stabilizer).le_normalizer_map Stabilizer.subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

/-- The fixed space of the actual hexad kernel in any binary action is
invariant under the hexad stabilizer. -/
def kernelFixedSubrepresentation {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) m22PairStabilizer V) :
    Subrepresentation (ρ.comp Stabilizer.subtype) where
  toSubmodule := fixedSpace ρ Kernel
  apply_mem_toSubmodule g v hv a := by
    have ha : g.val⁻¹ * a.val * g.val ∈ Kernel := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
        (stabilizer_le_normalizer (Stabilizer.inv_mem g.property)) a.val).mp a.property
    have he := hv ⟨g.val⁻¹ * a.val * g.val, ha⟩
    change ρ a.val (ρ g.val v) = ρ g.val v
    calc
      _ = ρ g.val (ρ (g.val⁻¹ * a.val * g.val) v) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      _ = ρ g.val v := congrArg (ρ g.val) he

/-- The actual hexad fixed code space, with its stabilizer action. -/
def codeFixedSubrepresentation :
    Subrepresentation (m22OuterCodeRepresentation.comp Stabilizer.subtype) :=
  kernelFixedSubrepresentation m22OuterCodeRepresentation

/-- The actual hexad fixed cocode space, with its stabilizer action. -/
def cocodeFixedSubrepresentation :
    Subrepresentation (m22OuterCocodeRepresentation.comp Stabilizer.subtype) :=
  kernelFixedSubrepresentation m22OuterCocodeRepresentation

/-- V5 as a subrepresentation, obtained from its proved annihilator formula. -/
def codeCommutatorSubrepresentation :
    Subrepresentation (m22OuterCodeRepresentation.comp Stabilizer.subtype) :=
  annihilatorSubrepresentation Stabilizer cocodeFixedSubrepresentation

theorem codeCommutatorSubrepresentation_space :
    codeCommutatorSubrepresentation.toSubmodule = codeCommutator Kernel :=
  (codeCommutator_eq_annihilator Kernel).symm

theorem codeFixedSubrepresentation_finrank
    (h : OuterRestrictionInput m22SourceOctad) :
    Module.finrank (ZMod 2) codeFixedSubrepresentation.toSubmodule = 1 :=
  code_fixedSpace_finrank (MonoidHom.id m22PairStabilizer) Kernel m22SourceOctad
    m22Pair_le_sourceOctad h.kernel_image

theorem codeCommutatorSubrepresentation_finrank
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    Module.finrank (ZMod 2) codeCommutatorSubrepresentation.toSubmodule = 5 := by
  rw [codeCommutatorSubrepresentation_space]
  exact codeCommutator_finrank Kernel (h.fixedSpace_finrank h24.displacement h24.fixed_finrank)

/-- The fixed line lies in every nonzero invariant subspace; here orbit
counting applies it to the genuine five-dimensional commutator space. -/
theorem codeFixed_le_commutator
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    codeFixedSubrepresentation.toSubmodule ≤ codeCommutator Kernel := by
  let W := codeCommutatorSubrepresentation.toSubmodule
  let τ : Representation (ZMod 2) Kernel W :=
    codeCommutatorSubrepresentation.toRepresentation.comp
      (Subgroup.inclusion kernel_le_stabilizer)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : MulAction Kernel W := {
    smul a w := τ a w
    one_smul w := by change τ 1 w = w; simp
    mul_smul a b w := by change τ (a * b) w = τ a (τ b w); simp }
  have hdim : Module.finrank (ZMod 2) W = 5 :=
    codeCommutatorSubrepresentation_finrank h h24
  have hdiv : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    decide
  have hp : IsPGroup 2 Kernel :=
    (pCore_isPGroup (p := 2) (G := Stabilizer)).map Stabilizer.subtype
  have hz : (0 : W) ∈ MulAction.fixedPoints Kernel W := fun a => map_zero (τ a)
  obtain ⟨v, hv, hne⟩ :=
    hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdiv hz
  have hv0 : v.val ≠ 0 := fun he => hne (Subtype.ext he.symm)
  have hvf : v.val ∈ codeFixedSubrepresentation.toSubmodule := by
    intro a
    exact congrArg Subtype.val (hv a)
  have hline : codeFixedSubrepresentation.toSubmodule =
      Submodule.span (ZMod 2) {v.val} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (codeFixedSubrepresentation_finrank h)
      hvf hv0
  rw [hline]
  apply Submodule.span_le.mpr
  rw [Set.singleton_subset_iff]
  exact codeCommutatorSubrepresentation_space ▸ v.property

theorem codeFixed_lt_commutator
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    codeFixedSubrepresentation.toSubmodule < codeCommutator Kernel := by
  apply lt_of_le_of_ne (codeFixed_le_commutator h h24)
  intro he
  have h1 := codeFixedSubrepresentation_finrank h
  rw [he, codeCommutator_finrank Kernel
    (h.fixedSpace_finrank h24.displacement h24.fixed_finrank)] at h1
  omega

theorem code_prefix_strict
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    ⊥ < codeFixedSubrepresentation.toSubmodule ∧
      codeFixedSubrepresentation.toSubmodule < codeCommutator Kernel ∧
      codeCommutator Kernel < ⊤ := by
  have h1 := codeFixedSubrepresentation_finrank h
  have h5 := codeCommutator_finrank Kernel
    (h.fixedSpace_finrank h24.displacement h24.fixed_finrank)
  refine ⟨?_, codeFixed_lt_commutator h h24, ?_⟩
  · apply bot_lt_iff_ne_bot.mpr
    intro he
    rw [he, finrank_bot] at h1
    omega
  · apply lt_top_iff_ne_top.mpr
    intro he
    rw [he, finrank_top, finrank_m22Code] at h5
    omega

/-- The H.14 displacement transferred through the actual coordinate pairing. -/
theorem code_element_fixed_finrank (h : OuterRestrictionInput m22SourceOctad)
    (a : m22PairStabilizer) (ha : a ∈ Kernel) (ha1 : a ≠ 1) :
    Module.finrank (ZMod 2)
      (fixedSpace m22OuterCodeRepresentation (Subgroup.zpowers a)) = 6 := by
  have hd := (fixedSpace m22OuterCodeRepresentation
    (Subgroup.zpowers a)).finrank_quotient_add_finrank
  have h4 : fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers a) = 4 :=
    h.displacement a ha ha1
  change fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers a) + _ = _ at hd
  rw [code_cocode_fixedCodim, h4, finrank_m22Code] at hd
  omega

/-- The fixed space in the literal code quotient V/C_V(K), with K taken
inside its own normalizer rather than declared normal in the ambient group. -/
def fixedCodeQuotient : Submodule (ZMod 2)
    (M22Code ⧸ codeFixedSubrepresentation.toSubmodule) :=
  fixedSpace codeFixedSubrepresentation.quotientRepresentation (Kernel.subgroupOf Stabilizer)

/-- The actual image of [V,K] in V/C_V(K). -/
def commutatorImage : Submodule (ZMod 2)
    (M22Code ⧸ codeFixedSubrepresentation.toSubmodule) :=
  (codeCommutator Kernel).map codeFixedSubrepresentation.toSubmodule.mkQ

end MathieuCode.Hexad.ChiefFlag
