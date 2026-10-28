module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Local
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Borel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Geometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Factors

/-!
# Block recognition in the L₂ branch of 15.3.30

The marked matrix Borel lifts through the central kernel of the action of
L/O₂(L). It makes Y₊ normalize L ∩ S and gives the unique maximal overgroups
required by B.6.1, both for I over S and for LR over R = O₂(Y₊S).

Apply C.1.26 to I. The actual Sylow embedding transports 15.3.29 and excludes
both distinguished characteristic-subgroup alternatives. The remaining
central product generates O²(I) = L. Quasisimplicity of L/O₂(L) and
two-perfectness identify L with one of its factors; perfectness excludes
the A₃ type. The result retains the genuine quotient and natural module
of an L₂ or A₅ block, with subnormality relative to I.

Applying C.1.26 to I is essential to this argument: 15.3.29 concerns S,
and does not say that characteristic subgroups of R are characteristic in S.
The separate LR geometry and its characteristic-two and SQTK hypotheses
are also retained. The universal C.1.26 implication, its distinguished
choices, the local SQTK catalogue hypothesis, and the stated earlier
conclusions remain explicit inputs for the source-theorem assembly owner.
The final exclusion in 15.3.30 is outside this block-recognition step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.6.1,
C.1.26, and 15.3.30, printed pp.112, 132, and 1131–1132.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}

/-- Conditional block recognition in 15.3.30 from the actual marked Borel.
The two extra local clauses are 15.3.11(2) and 15.3.29(1). Minimal
parabolicity and the residual block product are constructed in the proof;
the universal earlier theorem C.1.26 and local SQTK remain explicit. -/
theorem block_recognition_of_borel
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (d : LocalData G) {I : Subgroup G} {c : ComponentWitness d I}
    (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (hSQTK : IsSQTK 𝒦 I) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]
    (b : BorelIdentification d I c n F)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hpush : ∀ A : Subgroup d.S, A.Characteristic → A ≠ ⊥ →
      ¬ ((A.map d.S.subtype).subgroupOf I).Normal) :
    ChapterC.IsBlock (c.L.subgroupOf I) ∧
      ((∃ m, ChapterC.IsL2EvenBlock c.L m) ∨ ChapterC.IsAlternatingBlock c.L 5) := by
  have hpar := Geometry.minimalParabolic_I b h hI P hP hc
  obtain ⟨product⟩ := blockProduct_on_I choices source d hSQTK hf P hP hpar hpush
  exact block_recognition d h hI P hP product

/-- The block alternatives together with the literal LR geometry of 15.3.30.
The local hypotheses for C.1.26 hold in both I and LR, but the application
uses I so that its Sylow subgroup is the S of 15.3.29. -/
theorem local_block_recognition
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (d : LocalData G) {I : Subgroup G} {c : ComponentWitness d I}
    (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (hSQTK : IsSQTK 𝒦 I) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]
    (b : BorelIdentification d I c n F)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hpush : ∀ A : Subgroup d.S, A.Characteristic → A ≠ ⊥ →
      ¬ ((A.map d.S.subtype).subgroupOf I).Normal) :
    (ChapterC.IsBlock (c.L.subgroupOf I) ∧
      ((∃ m, ChapterC.IsL2EvenBlock c.L m) ∨ ChapterC.IsAlternatingBlock c.L 5)) ∧
    d.Yplus ≤ normalizer ((c.L ⊓ d.S : Subgroup G) : Set G) ∧
    d.Yplus.subgroupOf I ≤ normalizer
      ((c.L.subgroupOf I ⊓ (P : Subgroup I) : Subgroup I) : Set I) ∧
    ChapterB.IsMinimalParabolicOver P ⊤ ∧
    HasCharacteristicTwo (c.L ⊔ d.R) ∧
    IsSQTK 𝒦 (c.L ⊔ d.R : Subgroup G) ∧
    ∃ Q : Sylow 2 ↥(c.L ⊔ d.R),
      (Q : Subgroup ↥(c.L ⊔ d.R)).map (c.L ⊔ d.R).subtype = d.R ∧
      ChapterB.IsMinimalParabolicOver Q ⊤ := by
  obtain ⟨hY, hpar, hLR⟩ := Geometry.local_geometry b h hI P hP hc
  exact ⟨block_recognition_of_borel choices source d hI hf hSQTK h P hP b hc hpush,
    hY, Geometry.yplus_normalizes_intersection_in_I b h P hP, hpar,
    characteristicTwo_LR d c hI.1 hf P hP, sqtk_LR d c hI.1 hSQTK, hLR⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

end
