module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.G64Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Applicability
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# The source setting for the component-section application

We retain the actual quotient L/O₂,Z(L) ≃ A₆, its conjugation action on the
four-dimensional natural V, the complete Sylow-invariant flag, the source
normalizers, and the abelian conjugate span. The quotient by the central
preimage retains both the ordinary and covered A₆ possibilities. The line's
order two supplies the genuine two-local witness needed for the SQTK cover.

These are relevant standing input data, not a claim to have proved the earlier
source reductions. The source centralizer identity from F.9.2(3), recalled in
Notation 13.5.8 and at the start of §13.8, remains an explicit earlier input
of the application. No recognized component or section occurs in these data.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation
13.2.1, p.877; 13.5.2(3) and the flag convention, pp.915–916; Notation
13.5.8, p.918; the counterexample setup and 13.8.2, p.946.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual A₆ quotient, its natural action on V, and the source flag.
The quotient is L/O₂,Z(L), so the triple-cover case is retained. -/
structure SourceA6Flag (T : Sylow 2 G) (L V V₁ V₂ V₃ : Subgroup G) where
  model : (L ⧸ centralPreimage (pCore 2 L)) ≃* alternatingGroup (Fin 6)
  normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G)
  normalizes_V : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
  coordinate : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6))
  conjugation : ∀ (l : L) (v : V),
    (coordinate (V.normalizerMonoidHom
      ⟨l.val, normalizes_V (show l.val ∈ L ⊔ T from
        (show L ≤ L ⊔ T from le_sup_left) l.property)⟩ v)).toAdd =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (model (QuotientGroup.mk' (centralPreimage (pCore 2 L)) l)) (coordinate v).toAdd
  point : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6))
  plane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6))
  hyperplane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6))
  point_dim : Module.finrank (ZMod 2) point = 1
  plane_dim : Module.finrank (ZMod 2) plane = 2
  hyperplane_dim : Module.finrank (ZMod 2) hyperplane = 3
  point_le_plane : point ≤ plane
  plane_le_hyperplane : plane ≤ hyperplane
  line_eq : V₁ = TransvectionParabolic.EarlierCore.flagPreimage coordinate point
  plane_eq : V₂ = TransvectionParabolic.EarlierCore.flagPreimage coordinate plane
  seed_eq : V₃ = TransvectionParabolic.EarlierCore.flagPreimage coordinate hyperplane
  line_stable : (T : Subgroup G) ≤ normalizer (V₁ : Set G)
  plane_stable : (T : Subgroup G) ≤ normalizer (V₂ : Set G)
  seed_stable : (T : Subgroup G) ≤ normalizer (V₃ : Set G)

/-- The genuine counterexample assumptions relevant to this step. These retain
the source model and flag and abelian closure, even though the general
recognition argument works with fewer hypotheses. The earlier centralizer
identity is supplied separately; no component or recognized section is a field. -/
structure SourceContext (κ : GroupClass.{u}) (T : Sylow 2 G)
    (L V V₁ V₂ V₃ G₁ M : Subgroup G) where
  qtke : IsSimpleQTKE κ G
  not_symplectic : ¬ ClassicalGroup.IsPSp G 3 2
  not_unitary : ¬ ClassicalGroup.IsPSU G 4 3
  flag : SourceA6Flag T L V V₁ V₂ V₃
  point_normalizer : G₁ = normalizer (V₁ : Set G)
  module_normalizer : M = normalizer (V : Set G)
  abelian_closure : IsMulCommutative (conjugateSpanBy V G₁)

omit [Finite G] in
/-- The actual line has order two, so its normalizer is a two-local subgroup.
This constructs the two-local witness from the flag, rather than assuming it. -/
theorem SourceA6Flag.line_two_local {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : SourceA6Flag T L V V₁ V₂ V₃) : V₁ ≠ ⊥ ∧ IsPGroup 2 V₁ := by
  have hc : Nat.card V₁ = 2 := by
    rw [d.line_eq, TransvectionParabolic.EarlierCore.flagPreimage_card, d.point_dim, pow_one]
  refine ⟨?_, IsPGroup.of_card (n := 1) (by simpa using hc)⟩
  intro he
  rw [he, Subgroup.card_bot] at hc
  omega

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

end
