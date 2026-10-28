module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Setup
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.Words
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Fusion.Orbit

/-!
# Concrete words for seven-coordinate fusion

Signed letters 1 and 2 name the two indicated generators; products are read
left to right. The local normalizer words and the ambient/local conjugator
pairs were produced by the parent's `ShortNormalizer.g`, `SearchFusion.py`
and `SearchLocalFusion.py`. These definitions assert no matrix identities;
the two certificate propositions below record the exact remaining obligations.
Original matrices and attribution: `refs/original/onan/README.md`.
-/

@[expose] public section
namespace ONan.Simplicity.Seven.Fusion

/-- Evaluate a signed word in any two group elements. -/
def word {G : Type*} [Group G] (a b : G) (w : List ℤ) : G :=
  (w.map (fun i => if i = 1 then a else if i = -1 then a⁻¹ else
    if i = 2 then b else if i = -2 then b⁻¹ else 1)).prod

/-- The five actual words proposed to realize the coordinate substitutions. -/
def normalizer : Fin 5 → Model :=
  ![generatorX, generatorY, generatorZ,
    word ONan.OrderCertificate.localA ONan.OrderCertificate.localB [1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2],
    word ONan.OrderCertificate.localA ONan.OrderCertificate.localB [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2]]

/-- A local word conjugating Z to Y. -/
def centralBridge : Model :=
  word ONan.OrderCertificate.localA ONan.OrderCertificate.localB [-2, 1, 2, 1, 2, 2, 1, 2, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1]

/-- Ambient/local products conjugating X, Y and XY to the fixed representatives. -/
def rootConjugator : Fin 3 → Model :=
  ![word generatorA generatorB [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2] *
      word ONan.OrderCertificate.localA ONan.OrderCertificate.localB [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2],
    word generatorA generatorB [1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2] *
      word ONan.OrderCertificate.localA ONan.OrderCertificate.localB [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2],
    word generatorA generatorB [1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1] *
      word ONan.OrderCertificate.localA ONan.OrderCertificate.localB [1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2]]

/-- X and Y map to index 3; XY maps to index 4. -/
def rootRepresentative : Fin 3 → Fin 8 := ![3, 3, 4]

/-- Fifteen generator equations imply all five actions on every normal form. -/
def NormalizerIdentities : Prop :=
  ∀ (j : Fin 5) (r : Fin 3),
    (normalizer j)⁻¹ * evaluate (basis r) * normalizer j =
      evaluate (generatorImage j r)

/-- Three ambient fusion equations and the central-to-root bridge. -/
structure RootIdentities : Prop where
  roots : ∀ r : Fin 3,
    primeRepresentative (rootRepresentative r) =
      rootConjugator r * evaluate (origin ⟨r.val, by omega⟩) * (rootConjugator r)⁻¹
  central : centralBridge⁻¹ * generatorZ * centralBridge = generatorY

end ONan.Simplicity.Seven.Fusion
