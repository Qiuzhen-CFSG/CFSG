module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.LocalSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.CoreQuotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.ActionKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry

/-!
# The natural module and fixed geometry in 15.3.32

`natural_module_of_source` constructs the natural degree-eight action on the
actual component commutator `U_L`, retaining the original star marking. The
FF classification is applied to the offender-generated actor, whose faithful
binary action, trivial two-core, generalized Fitting subgroup and offender
generation are proved in `Recognition`. The actual moving plane
`V₂ = [V₂,Y₊]` and middle-node marking exclude the natural-plus-dual and
repeated-natural alternatives. The Sylow action on that plane also excludes
a nontrivial orthogonal covering, giving the six-dimensional natural module.

The marked `A₈` perfect-cover argument identifies the component and ambient
core quotients; faithfulness then gives `O₂(I) = C_I(U_L) = C_S(U_L)`.
`coreEquivEight_map` transports every subgroup marking through the same
quotient map. Applying B.2.14 to the genuine `U_I = ⟨Z^I⟩` supplies its central
summand. The Sylow fixed-space bound and the two definite planes identify
`C_{Z_S}(L) = Z_S ∩ V₁`, of order two, and `Z_S ∩ U_L = Z_S ∩ V₂`.

This completes the conditional natural-module task: no action, module
coordinates, local centralizer equality or fixed-plane identity is assumed.
The explicit universal inputs are B.5.1(1)/B.4.2, I.1.6(6) for the dual
natural L₄(2) and L₅(2) modules, the I.1.3 multiplier consequence, and the
splitting clause of B.2.14(1). The parent supplies the actual component's
SQTK hypothesis, the marked 15.3.28(3) conclusion, and the genuine preliminary
facts. In particular the seed-span containment is the one used in the proof
of 15.3.11 on p.1124. The remaining clauses of 15.3.32 belong to EightGeometry.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.2–11, 15.3.28(3), and 15.3.32 with its preceding paragraph, printed
pp.1121–1124 and 1131–1133; B.2.14, B.4.2, B.5.1 and I.1.3–6.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule

universe u
variable {G : Type u} [Group G] [Finite G]
  (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hnormal : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
  (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
  (e : d.Star I ≃* Equiv.Perm (Fin 8))
  (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
  (hcover : EightCoverKernelTwo.{u})

/-- The intrinsic core quotient with the originally supplied degree-eight marking. -/
noncomputable def coreEquivEight : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8) :=
  (coreEquivStar d c hnormal hI P hP e hmark hcover).trans e

/-- The comparison uses exactly the original star projection. -/
@[simp] theorem coreEquivEight_apply (i : I) :
    coreEquivEight d c hnormal hI P hP e hmark hcover
      (QuotientGroup.mk' (pCore 2 I) i) = e (d.starMap I i) := rfl

/-- Every subgroup image retains its original marking, including the component,
the Sylow image and both parabolics. No conjugacy change is made. -/
theorem coreEquivEight_map (X : Subgroup G) :
    ((X.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))).map
        (coreEquivEight d c hnormal hI P hP e hmark hcover).toMonoidHom =
      (d.starImage I X).map e.toMonoidHom := by
  change ((X.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))).map _ =
    ((X.subgroupOf I).map (d.starMap I)).map e.toMonoidHom
  rw [map_map, map_map]
  rfl

include hnormal hI P hP hmark hcover in
/-- The natural-module and fixed-geometry conclusions of 15.3.32, from the
universal earlier source inputs and the genuine preliminary conclusions.
The action is constructed here, and its actor preserves the supplied marking. -/
theorem natural_module_of_source
    (classification : Recognition.FFSpecialization.Sieve.UniversalFFClassification.{u,u})
    (cohomology : Recognition.FFSpecialization.Sieve.UniversalNaturalCohomology)
    (splitting : FixedGeometry.SourceB214Splitting.{u})
    (hchar : HasCharacteristicTwo I)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple (d.starImage I c.L))
    (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (htheta : theta (d.MI I) = d.Yplus)
    (hnorm : I ⊓ normalizer (d.Yplus : Set G) = d.MI I)
    (hplane : ⁅d.V, d.Yplus⁆ = d.V₂)
    (hfull : ⁅d.V₂, d.Yplus⁆ = d.V₂)
    (hseed : d.V₂ ≤ localSpan d.Z d.Yplus)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (hOmega : d.ZS = Stellmacher.omegaOneCenterAmbient d.S)
    (mark : Recognition.Models.MiddleNodeMarking
      (d.starImage I c.L) (d.starImage I (d.M ⊓ c.L))) :
    ∃ a : NaturalEightAction I (d.componentModule I c.L),
      a.actor = e.toMonoidHom.comp (d.starMap I) ∧
      I.pCoreIn 2 = I ⊓ centralizer (d.componentModule I c.L : Set G) ∧
      I.pCoreIn 2 = d.S ⊓ centralizer (d.componentModule I c.L : Set G) ∧
      d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁ ∧
      Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2 ∧
      d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂ := by
  have hline : Recognition.LineData d I :=
    ⟨htheta, hnorm, hplane, hfull,
      hseed.trans (conjugateSpanBy_mono le_rfl (hYL.trans (component_le c)))⟩
  obtain ⟨a, hactor⟩ := Recognition.exists_action_of_source d c hnormal hI hchar P hP
    e hmark classification cohomology hSQTK hYL hline mark
  obtain ⟨hCI, hCS⟩ := centralizer_componentModule_eq_core d c hnormal hI P hP
    e hmark hcover a hactor
  exact ⟨a, hactor, hCI.symm, hCS.symm,
    FixedGeometry.fixed_geometry splitting d hchar c hnormal hI hYL hRank hYRank
      P hP hfull.symm hseed hindex hZ hZS hOmega e hmark a hactor⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule

end
