module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Section

/-!
# The remaining source branches in the construction of 14.7.63

The alternatives are isomorphisms of the actual residual quotient. The
natural-module conclusion is an equivariant surjection from the original
conjugation section, with exactly its K-fixed kernel. It contains no
indecomposability premise and assumes no Data record.

The conditional assembly eliminates the G₂ alternative, constructs the
literal binary section, and applies the preceding algebraic construction.
The missing source reduction through 14.7.52 (including 14.7.40) and the
14.7.53 exclusion are distinct obligations. Their final assembly remains
with qt-d-14763-source-data; this module does not assert either implication.

Source: Aschbacher–Smith, 14.7.40, 14.7.48, 14.7.52–53 and 14.7.63,
printed pp.1061–1069.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (F : InvariantFlag T V 3)

/-- The A₅ alternative for the literal K/O₂(K), not a group-family tag. -/
def AlternatingResidual : Prop :=
  Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* alternatingGroup (Fin 5))

/-- The other alternative in 14.7.52, using the concrete binary G₂ derived group. -/
def G2Residual : Prop :=
  Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))

/-- The natural quotient conclusion needed from 14.7.40, on any coordinates
for the same original section. The star map and the K-fixed kernel are literal. -/
def NaturalRecognition : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) F.H W),
    BinaryConjugationSection F.H F.U (F.Vi 1) ρ →
    ∃ (e : HStar F.H ≃* ChapterJ.S5) (a : ChapterJ.L2FourAction)
      (p : ρ.IntertwiningMap (a.action.comp (quotientMarking e))),
      Function.Surjective p ∧ p.toLinearMap.ker =
        Representation.invariants (ρ.comp ((K F).subgroupOf F.H).subtype)

variable {F}

/-- Conditional source assembly. The earlier recognition branches are
explicit; the section carrier, its action and indecomposability are constructed. -/
theorem exists_data_of_source_branches
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (h52 : AlternatingResidual F ∨ G2Residual F)
    (h53 : ¬ G2Residual F)
    (h40 : AlternatingResidual F → NaturalRecognition F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ, ⟨c⟩⟩ := exists_section F
  obtain ⟨e, a, p, hp, hk⟩ := h40 (h52.resolve_right h53) _ ρ c
  exact ⟨Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U), inferInstance, inferInstance,
    ⟨data_of_recognition d h hab hunique hcomponent c e a p hp hk⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction
