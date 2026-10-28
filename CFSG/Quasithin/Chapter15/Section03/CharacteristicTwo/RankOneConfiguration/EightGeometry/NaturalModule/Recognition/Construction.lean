module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.NaturalDualExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting

/-!+# Constructing the natural action with the original degree-eight marking

Apply the universal B.5.1/B.4.2 table at the offender-generated actor of the
actual component module. Its FF hypotheses, including `[U_L,L] = U_L`, are
proved by `FFSpecialization`; this actor need not be the whole star quotient.
The actual V₂ plane and middle-node parabolic exclude the natural-plus-dual
and repeated-natural branches. The same Sylow-invariant moving plane rules
out a nontrivial orthogonal cover. Rigidity then extends the component
coordinates to the entire originally marked S₈ action, and conjugation
compatibility gives the action on the original subgroup U_L.

Only two universal earlier source inputs remain: the full forgetful
B.5.1(1)/B.4.2 table `Sieve.UniversalFFClassification` and the I.1.6(6)
vanishing `Sieve.UniversalNaturalCohomology` for the dual natural L₄(2)
and L₅(2) modules. Both are independent of this local configuration.
The SQTK premise uses the full known-simple catalogue on the actual
component image. `LineData` and the Sylow witness are genuine preliminary
conclusions, and `MiddleNodeMarking` is the conclusion of 15.3.28(3).
No recognized module or coordinates are input to the construction.

The elementary abelian structure is derived internally. Minimality, rank one
and solvable invariant control were used upstream to obtain the supplied
component, normality, product, Sylow and parabolic conclusions; no additional
use of them is needed here. This completes the conditional action construction,
not the earlier universal source theorems or the remaining clauses of 15.3.32.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2,
B.5.1(1), I.1.5–I.1.6 and 15.3.32(1), printed pp.86, 99–103, 408
and 1132–1133.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition

universe u
variable {G : Type u} [Group G] [Finite G]
  (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
  (hchar : HasCharacteristicTwo I)
  (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
  (e : d.Star I ≃* Equiv.Perm (Fin 8))
  (he : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
  (classification : FFSpecialization.Sieve.UniversalFFClassification.{u,u})
  (cohomology : FFSpecialization.Sieve.UniversalNaturalCohomology)
  (hSQTK : IsSQTK KnownSimple.IsKnownSimple (d.starImage I c.L))
  (hYL : d.Yplus ≤ c.L) (hline : LineData d I)
  (mark : Models.MiddleNodeMarking (d.starImage I c.L) (d.starImage I (d.M ⊓ c.L)))

include hn hI hchar P hP e he classification cohomology hSQTK hYL hline mark

/-- The earlier universal source results give coordinates equivariant for every
element of the original star quotient, without changing its S₈ marking. -/
theorem coordinates_of_source
    [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)] :
    ∃ f : Additive ((d.componentModule I c.L).subgroupOf I) ≃ₗ[ZMod 2]
        BinaryPermutation.natural (Fin 8),
      ∀ g v, f (componentAction d c hn hI hchar P hP g v) =
        BinaryPermutation.naturalRepresentation (Fin 8) (e g) (f v) := by
  have line := hline.movingLine d c hn hI hchar P hP hYL
  rcases FFSpecialization.alternatives_of_source d c hn hI hchar P hP e he
      classification cohomology hSQTK hYL hline mark with cover | dual
  · obtain ⟨cover⟩ := cover
    have sylowLine : Models.MovingLine (componentAction d c hn hI hchar P hP)
        (d.starImage I (d.M ⊓ c.L)) (starSylow d P : Subgroup (d.Star I))
        (d.starImage I d.Yplus) := by
      rw [starSylow_coe d P hP]
      exact line
    obtain ⟨f, _, hf⟩ := CoverSplitting.coordinates
      (componentAction d c hn hI hchar P hP) e (d.starImage I c.L) he cover
      (starSylow d P) sylowLine
    exact ⟨f, hf⟩
  · exact (NaturalDualExclusion.not_nonempty_naturalDual mark line
      (hline.yplus_star_le_parabolic d c hYL) dual).elim

/-- Construct the actual subgroup action, deriving its binary structure from
characteristic two. Its actor is exactly the supplied marking of the star map. -/
theorem exists_action_of_source :
    ∃ a : NaturalEightAction I (d.componentModule I c.L),
      a.actor = e.toMonoidHom.comp (d.starMap I) := by
  let _ := component_internal_elementary d c hchar P hP
  obtain ⟨f, hf⟩ := coordinates_of_source d c hn hI hchar P hP e he
    classification cohomology hSQTK hYL hline mark
  exact ⟨actionOfCoordinates d c hn hI hchar P hP e f hf,
    actionOfCoordinates_actor d c hn hI hchar P hP e f hf⟩

/-- The natural-eight action obtained from the two explicit universal source
inputs and the genuine earlier local and middle-node conclusions. -/
noncomputable def actionOfSource : NaturalEightAction I (d.componentModule I c.L) :=
  Classical.choose (exists_action_of_source d c hn hI hchar P hP e he
    classification cohomology hSQTK hYL hline mark)

/-- The constructed action preserves the original S₈ marking exactly. -/
theorem actionOfSource_actor :
    (actionOfSource d c hn hI hchar P hP e he
      classification cohomology hSQTK hYL hline mark).actor =
        e.toMonoidHom.comp (d.starMap I) :=
  Classical.choose_spec (exists_action_of_source d c hn hI hchar P hP e he
    classification cohomology hSQTK hYL hline mark)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition

end
