module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearField
public import CFSG.Quasithin.ChapterF.Section08.Closure
public import CFSG.Quasithin.ChapterF.Section09.Setup

/-!
# Literal local inputs for the escaping cubic branch

The source selects z in the Sylow omega-center and defines
V₂ = ⟨⟨z⟩^C⟩ and L₂ = ⟨C^T⟩. These definitions retain the original cubic,
Sylow and H. The local data below are construction targets from 5.1.21--22
and the kernel argument after 5.1.23. They do not assert existence,
abelianness of the point-centralizer span, or a quadratic-ratio bound.

The abelian-span argument and its strict-ratio counterpart have an
independent representation-theoretic proof in 5.1.23. The assembly must
supply both those results and these local data.

Source: Aschbacher--Smith, 5.1.21--23 and the final paragraph of 5.1.14,
printed pp.644--646 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G]

def plane (C : Subgroup G) (z : G) : Subgroup G := conjugateSpanBy (zpowers z) C
def actor (T : Sylow 2 G) (C : Subgroup G) : Subgroup G :=
  conjugateSpanBy C (T : Subgroup G)
def setup (T : Sylow 2 G) (H C : Subgroup G) (z : G) : ChapterG.Section02.Setup G :=
  ⟨plane C z, zpowers z, actor T C, T, H⟩
def f9Setup (T : Sylow 2 G) (H C : Subgroup G) (z : G) : ChapterF.Section09.Setup G :=
  ⟨T, actor T C, plane C z, plane C z, zpowers z, H⟩

/-- The earlier local source statements needed at the final application.
Every group and quotient is fixed by T,H,C,z; no arbitrary action or
classification witness is supplied. The abelian span is deliberately separate. -/
structure LocalData [Finite G] (T : Sylow 2 G) (H C : Subgroup G) (z : G) : Prop where
  point_mem : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  point_ne : z ≠ 1
  plane_card : Nat.card (plane C z) = 4
  transitive : ∀ x ∈ plane C z, x ≠ 1 → ∃ l ∈ actor T C, (MulAut.conj l) z = x
  g2 : (setup T H C z).Hypothesis
  characteristic_actor : generalizedFitting (actor T C) = pCore 2 (actor T C)
  plane_le : plane C z ≤ actor T C ⊔ (T : Subgroup G)
  reduced : IsPReduced 2 ((plane C z).subgroupOf (actor T C ⊔ (T : Subgroup G)))
  centralizer_eq : (T : Subgroup G) ⊓ centralizer (plane C z : Set G) =
    (actor T C ⊔ (T : Subgroup G)).pCoreIn 2
  kernel_core : (ChapterF.Section08.Setup.quotientCentralizer
    (setup T H C z) g2.H_le (plane C z)).normalCore ≤
    pCore 2 H
  generated_core : pCore 2 ((actor T C ⊔ (T : Subgroup G)) ⊔ H : Subgroup G) = ⊥

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
