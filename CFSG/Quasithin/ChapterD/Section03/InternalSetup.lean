module

public import CFSG.Quasithin.ChapterD.Section03.SourceSetup
public import Theory.GroupTheory.CComponent.QuasisimpleImage
public import Theory.GroupTheory.PResidual.Defs
public import Theory.Representation.BinaryOffender.ActionImage

/-!
# The internal actor and module hypotheses for D.3.3

The two internal actor alternatives retain the C-component and its
intrinsic quasisimple two-core quotient, or the odd-prime quotient together
with its actual irreducible conjugation action above O₂,Φ. The module
version records exactly the linear-action assumptions extracted from the
elementary section in Hypothesis D.3.2. Its faithful orbit image is a
construction, rather than an assumed conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis D.3.2 and Lemma D.3.3, printed p.193.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u v
variable {G : Type u} [Group G]

/-- The intrinsic O₂,Φ(X), with its actual quotient preimage. -/
def coreFrattiniIn (X : Subgroup G) : Subgroup X :=
  (frattini (X ⧸ pCore 2 X)).comap (QuotientGroup.mk' (pCore 2 X))

instance coreFrattiniIn_characteristic (X : Subgroup G) :
    (coreFrattiniIn X).Characteristic := Characteristic.comap_quotient_mk inferInstance

/-- The literal T-conjugation action on X/O₂,Φ(X). -/
def coreFrattiniAction (T X : Subgroup G) (hTX : T ≤ normalizer (X : Set G)) :
    T →* MulAut (X ⧸ coreFrattiniIn X) :=
  (quotientAut (coreFrattiniIn X)).comp
    (X.normalizerMonoidHom.comp (inclusion hTX))

def CoreFrattiniIrreducible (T X : Subgroup G)
    (hTX : T ≤ normalizer (X : Set G)) : Prop :=
  ∀ A : Subgroup (X ⧸ coreFrattiniIn X),
    (∀ t : T, ∀ a ∈ A, coreFrattiniAction T X hTX t a ∈ A) → A = ⊥ ∨ A = ⊤

/-- Both original alternatives of D.3.2, prior to passing to the action image. -/
def InternalActorCases (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G)) : Prop :=
  (∃ L : Subgroup G, L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L) ∧
      X = componentOrbit L (T : Subgroup G)) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p (X ⧸ pCore 2 X) ∧
      CoreFrattiniIrreducible (T : Subgroup G) X hTX)

/-- The literal representation assumptions extracted from D.3.2's
elementary section. The source section is supplied by its conjugation map;
the conclusions below apply to any representation with these hypotheses. -/
structure InternalModuleHypotheses (K : GroupClass.{u}) [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (X : Subgroup G) (I : Submodule (ZMod 2) V) : Prop where
  sqtk : IsSQTK K G
  finiteModule : Module.Finite (ZMod 2) V
  normal : X.Normal
  residual : pResidual 2 X = ⊤
  cases : InternalActorCases T X (by rw [normalizer_eq_top]; exact le_top)
  actorCore : pCore 2 (actionImage (ρ.comp X.subtype)) = ⊥
  seed : IsIrrPlus ρ X I
  coreInvariant : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ subspaceStabilizer ρ I

end CFSG.Quasithin.ChapterD.Section03
