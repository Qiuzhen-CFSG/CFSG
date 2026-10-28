module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Central
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesFixedComplete

/-!
# The central-part and TI conclusions of 11.0.3

The completed fixed-space branch of 3.2.5 identifies the original chosen
seed with its normalizer orbit whenever its central part is nonzero.
Combining this with the actual natural central-cover calculations proves
11.0.3(3), including nonsplit extensions. The fixed-free TI result and this
orbit equality give 11.0.3(4). In the nonzero-central-part branch every
intersection with the normalizer also normalizes the original seed.

Source: Aschbacher--Smith, 11.0.3(3--5), printed p.760, using 3.2.5.
The homogeneous quotient and the remaining fixed-free branch of (5) are
separate conclusions; neither is assumed here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The nonzero central part forces equality with the literal full module. -/
theorem fullModule_eq_of_centralizer_ne_bot
    (hc : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    componentOrbit V (normalizer (L : Set G)) = V :=
  ChosenModule.normalizerOrbit_eq_of_fixedSpace_ne_bot_of_many D S.source S.many hc

/-- Source 11.0.3(3), with the earlier fixed-space implication discharged. -/
theorem central_alternatives :
    (V ⊓ centralizer (L : Set G) = ⊥ ∧
      componentOrbit V (normalizer (L : Set G)) ⊓ centralizer (L : Set G) = ⊥) ∨
    ((Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))) ∧
      V = componentOrbit V (normalizer (L : Set G)) ∧
      Representation.BinaryOffender.rank (V ⊓ centralizer (L : Set G)) ≤ S.field.degree ∧
      L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆) :=
  central_alternatives_of_fixedSpace_invariance D S
    (ChosenModule.normalizerOrbit_eq_of_fixedSpace_ne_bot D S.source.toHypothesis1221)

/-- Source 11.0.3(4): the chosen seed is a TI-set under N_G(L). -/
theorem seed_ti (g : G) (hg : g ∈ normalizer (L : Set G)) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V :=
  ti_of_fixedSpace_invariance D S
    (ChosenModule.normalizerOrbit_eq_of_fixedSpace_ne_bot D S.source.toHypothesis1221) g hg

/-- Normalizer invariance in the nonzero-central-part branch of 11.0.3(5). -/
theorem normalizer_le_of_centralizer_ne_bot
    (hc : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    normalizer (L : Set G) ≤ normalizer (V : Set G) := by
  have h := le_normalizer_componentOrbit V (normalizer (L : Set G))
  rw [fullModule_eq_of_centralizer_ne_bot D S hc] at h
  exact h

/-- The actual relative intersection conclusion in this branch, for any H. -/
theorem intersection_normalizes_of_centralizer_ne_bot
    (hc : V ⊓ centralizer (L : Set G) ≠ ⊥) (H : Subgroup G) :
    H ⊓ normalizer (L : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (V : Set G) :=
  le_inf inf_le_right (inf_le_right.trans (normalizer_le_of_centralizer_ne_bot D S hc))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
