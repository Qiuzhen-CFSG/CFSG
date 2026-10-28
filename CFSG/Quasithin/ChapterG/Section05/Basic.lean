module

public import Theory.Representation.BinaryDuadModule.IncidenceRank
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The concrete permutation-module setup for G.5

Here G is the actual alternating group on six letters, and G₁ and G₂ are the
incident duad and syntheme stabilizers containing the standard Sylow two-group.
The equivariant coset bijection identifies Ω = G/G₁ with the fifteen duads.
The binary permutation module splits as the even-weight core and the constant
line, proving G.5.3(1). The perpendicular-complement map embeds the natural
four-dimensional module. The geometric middle space is the span of actual
line complements, with ranks 14, 9, 4 and both quotient ranks five.

These are the concrete inputs for the remaining cover and radical calculations;
no identification with a radical power or exhaustive simple-module catalogue
is assumed. Source: Aschbacher–Smith, combined manuscript (1 March 2004),
G.5, printed pp.342–345 (PDF pp.353–356).
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation
namespace CFSG.Quasithin.ChapterG.Section05

abbrev G := A6
abbrev G0 := S6
abbrev G1 := a6DuadStabilizer
abbrev G2 := a6SynthemeStabilizer
abbrev Omega := Duad
abbrev U := Full Omega
abbrev U0 := core Omega
noncomputable abbrev action := BinaryDuadModule.alternatingPointAction
noncomputable abbrev naturalAction := BinaryDuadModule.alternatingNaturalAction
abbrev lineComplementSpan := BinaryDuadModule.lineComplementSpan
noncomputable abbrev naturalSubmodule := BinaryDuadModule.complementSubrepresentation

private theorem orbit_eq_iff (g h : G) :
    g • (0 : Omega) = h • (0 : Omega) ↔ g⁻¹ * h ∈ G1 := by
  change g • (0 : Duad) = h • (0 : Duad) ↔ g⁻¹ * h ∈ a6DuadStabilizer
  rw [← a6_duad_stabilizer_zero]
  change _ ↔ (g⁻¹ * h) • (0 : Omega) = (0 : Omega)
  rw [mul_smul, inv_smul_eq_iff]
  exact eq_comm

/-- The literal left-coset action in G.5 is the duad action. -/
noncomputable def cosetMap : G ⧸ G1 → Omega :=
  Quotient.lift (fun g => g • (0 : Omega)) (by
    intro g h hh
    exact (orbit_eq_iff g h).mpr (QuotientGroup.leftRel_apply.mp hh))

private theorem cosetMap_bijective : Function.Bijective cosetMap := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with | h g =>
      induction y using Quotient.inductionOn with | h h =>
        intro he
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((orbit_eq_iff g h).mp he))
  · intro d
    obtain ⟨g, hg⟩ := a6_duad_transitive 0 d
    exact ⟨(g : G ⧸ G1), hg⟩

noncomputable def cosetEquiv : G ⧸ G1 ≃ Omega :=
  Equiv.ofBijective cosetMap (by exact cosetMap_bijective)

@[simp] theorem cosetEquiv_mk (g : G) : cosetEquiv (g : G ⧸ G1) = g • (0 : Omega) := rfl

theorem cosetEquiv_equivariant (g : G) (x : G ⧸ G1) :
    cosetEquiv (g • x) = g • cosetEquiv x := by
  induction x using Quotient.inductionOn with | h h =>
    rw [MulAction.Quotient.smul_coe, cosetEquiv_mk, cosetEquiv_mk]
    exact mul_smul g h (0 : Omega)

/-- G.5.3(1): the full fifteen-point module is its even core plus the fixed line. -/
theorem permutation_decomposition : IsCompl U0 (constants Omega) :=
  core_isCompl_constants Omega (by decide)

theorem permutation_finrank : Module.finrank (ZMod 2) U = 15 := finrank_full Omega

theorem core_finrank : Module.finrank (ZMod 2) U0 = 14 := finrank_core Omega

/-- The source natural copy is given by the actual perpendicular-complement code. -/
noncomputable def naturalCopy : NaturalModule ≃ₗ[ZMod 2] naturalSubmodule.toSubmodule :=
  BinaryDuadModule.complementEquiv

theorem naturalCopy_equivariant (g : G) (v : NaturalModule) :
    naturalCopy (naturalAction g v) = naturalSubmodule.toRepresentation g (naturalCopy v) :=
  BinaryDuadModule.complementEquiv_equivariant g v

/-- Geometric containment used before identifying these spaces with radical powers. -/
theorem natural_le_lines_le_core :
    naturalSubmodule.toSubmodule ≤ lineComplementSpan ∧ lineComplementSpan ≤ U0 :=
  ⟨BinaryDuadModule.complementSubrepresentation_le_lineComplementSpan,
    BinaryDuadModule.lineComplementSpan_le_core⟩

/-- The ranks of the three literal spaces in the G.5.3 construction. -/
theorem layer_finranks :
    Module.finrank (ZMod 2) U0 = 14 ∧
    Module.finrank (ZMod 2) lineComplementSpan = 9 ∧
    Module.finrank (ZMod 2) naturalSubmodule.toSubmodule = 4 :=
  ⟨core_finrank, BinaryDuadModule.lineComplementSpan_finrank,
    BinaryDuadModule.complementSubrepresentation_finrank⟩

/-- Both sections that will be identified as covers in G.5.3 have dimension five. -/
theorem quotient_finranks :
    Module.finrank (ZMod 2) (U0 ⧸ lineComplementSpan.comap U0.subtype) = 5 ∧
    Module.finrank (ZMod 2) (lineComplementSpan ⧸
      naturalSubmodule.toSubmodule.comap lineComplementSpan.subtype) = 5 :=
  ⟨BinaryDuadModule.core_quotient_lineComplementSpan_finrank,
    BinaryDuadModule.lineComplementSpan_quotient_complement_finrank⟩

end CFSG.Quasithin.ChapterG.Section05
