module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Basic

/-!+# Intermediate outputs for the early distance-four proof

These records separate the initial factorization argument from the edge
calculations. They have no constructors in this file and are not additional
source hypotheses. The owner of EarlyFacts must construct them before using
their conclusions.

The offender implication spells out the obstruction used in the proof of
(4.6.3) and the later appeals to (4.6.2). The centralizer is computed on
V_alpha/Z_alpha, via the actual stabilizer quotient; the actor's Frattini
subgroup is intrinsic to A and then included in the original amalgam.
`Q_alpha.relIndex A` means [A : A intersection Q_alpha]. The final constructor
must prove this implication from the source, rather than assume an offender
classification for an unrelated representation.

The edge outputs include the containment from (4.6.4) because it is used again
in the derived-noncentrality argument. The paper prints two different (4.6.6)
assertions; only the first, the Q-index calculation, belongs to EdgeFacts.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.1)--(4.6.6), pp.900--903.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early

variable {M : Type*} [Group M] (R : Subgroup M) (geometry : Geometry R)

/-- Outputs of the initial factorization argument through (4.6.3).
No field is supplied as a hypothesis of the requested source constructor. -/
structure InitialFacts : Prop where
  center_le_B : ∀ a, color R a = false →
    (center (V R a)).map (V R a).subtype ≤ B R a (geometry.Z_normal a)
  offender_derived_le : ∀ a b, color R a = false → Adjacent R a b →
    ∀ A : Subgroup (FreeAmalgam R), A ≤ Q R b → ¬ A ≤ Q R a →
      (frattini A).map A.subtype ≤ Q R a →
      (radiusFixed geometry a A).relIndex (V R a) ≤ (Q R a).relIndex A →
      ⁅V R a, V R a⁆ ≤ U R a
  commutator_central : ∀ a, color R a = false →
    ⁅V R a, Q R a⁆ ≤ (center (V R a)).map (V R a).subtype

/-- Outputs of (4.6.4), (4.6.5) and the first assertion labeled (4.6.6).
They do not contain the later noncentrality or radius-center equality. -/
structure EdgeFacts : Prop where
  edge_commutator_le_Z : ∀ a b, color R a = false → Adjacent R a b →
    ⁅Z R a, Q R b⁆ ≤ Z R b
  commutator_le_Z : ∀ a, color R a = false → ⁅V R a, Q R a⁆ ≤ Z R a
  edge_commutator_card : ∀ a b, color R a = false → Adjacent R a b →
    Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4
  edge_Z_index : ∀ a b, color R a = false → Adjacent R a b →
    (Z R b).relIndex (Z R a) = 2
  edge_Q_index : ∀ a b, color R a = false → Adjacent R a b →
    (Q R a).relIndex (Q R b) = 4

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
