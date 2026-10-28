module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import Stellmacher.OmegaOneCenterMap

/-!+# The two remaining natural-block calculations in E.6.23

The local calculation identifies the proper overgroup as an L₂(4) block
and realizes the V-action by elements of the center of its actual Sylow
intersection with Q. The intrinsic calculation concerns centralizers of
noncentral elements of that omega-center in the natural L₂(4) block.
Neither contract is asserted here as a theorem.

The intrinsic calculation may be proved independently of the local
identification. Its natural module is the defining SL₂(4) module, retained
by IsL2EvenBlock; an A₅ quotient with a deleted permutation module does not
satisfy this specification merely because its module also has order 16.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7,
printed p.246, and E.6.23, printed p.254 (PDF pp.257 and 265).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase

universe u
variable {G : Type u} [Group G]

/-- The actual natural block, common Sylow intersection, and literal inner V-action. -/
def NaturalOvergroup (Q V X : Subgroup G) : Prop :=
  ChapterC.IsL2EvenBlock X 2 ∧
    ∃ S : Sylow 2 X, (S : Subgroup X).map X.subtype = X ⊓ Q ∧
      ∀ v ∈ V, ∃ z : X, z ∈ Stellmacher.omegaOneCenterAmbient (S : Subgroup X) ∧
        ∀ x : X, (z : G) * (x : G) * (z : G)⁻¹ = v * (x : G) * v⁻¹

/-- Outstanding local identification and action construction. The actual overgroup
is an input; its existence is the separate lifting task. -/
def ProperOvergroupModels (T : Sylow 2 G) (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∀ X : Subgroup G, L < X → CentralizerBlock A X →
          ChapterC.IsChiZeroBlock X → NaturalOvergroup (sylowCentralizer (T : Subgroup G) V) V X

/-- Outstanding intrinsic natural-module calculation, independent of the E.6 setup. -/
def NaturalFourCentralizers : Prop :=
  ∀ (D : Type u) [Group D] [Finite D], ChapterC.IsL2EvenBlock D 2 →
    ∀ (S : Sylow 2 D) (z : D), z ∈ Stellmacher.omegaOneCenterAmbient (S : Subgroup D) →
      z ∉ center D → IsPGroup 2 (centralizer ({z} : Set D))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
