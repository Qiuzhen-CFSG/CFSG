module

public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.Twisted
public import Theory.SpecificGroups.ReeF4.CentralCovers.PrimaryReduction

/-!
# The Ree prime-degree lifting inputs in the twisted multiplier assembly

The two local section calculations for actual Ree fixed-point groups feed
the existing twisted-family consumer. The prime-kernel quotient reduction
and transfer discharge every larger or mixed-order covering kernel, while
the two perfect root seeds discharge perfectness of each large Ree model.

The local section existence statements remain hypotheses. The independent
triality canonical-kernel and Parrott-lift inputs are retained unchanged;
this is a conditional connection, not the completed I.1.3 multiplier table.
The Ree parameter is m ≥ 1 throughout, and the Tits endpoint is separate.

Source: Aschbacher–Smith I.1.1–4, printed pp.407–408 of
`refs/quasithin.pdf`; GLS3, Section 6.1.
-/

public section

namespace CFSG.Quasithin.ChapterI.LieMultipliers.Twisted

open PerfectCentralCovering

universe u

/-- The literal local lift triangles discharge the Ree canonical-kernel
premise in the existing three-family source consumer. -/
theorem universalProjection_ker_eq_bot_of_ree_local_sections
    (htriality : ∀ (f : ℕ) (hf : 0 < f),
      (universalProjection (Triality.Standard.BinaryCarrier f hf)).ker = ⊥)
    (htits : ∃ g : Tits.ParrottGenerator → UniversalGroup Tits.ParrottGroup,
      Tits.SatisfiesParrottRelations g ∧
        ∀ i, universalProjection Tits.ParrottGroup (g i) = Tits.parrottGenerator i)
    (hreeTwo : ∀ (m : ℕ), 1 ≤ m →
      ∀ (F : Type) [Group F] [Finite F] (d : Cover F (ReeF4.Model m)),
        Nat.card d.toMonoidHom.ker = 2 →
          ∃ s : ReeF4.Parabolics.unipotent m →* F,
            d.toMonoidHom.comp s = (ReeF4.Parabolics.unipotent m).subtype)
    (hreeOdd : ∀ (m : ℕ), 1 ≤ m → ∀ (p : ℕ), p.Prime → p ≠ 2 →
      ∀ (F : Type) [Group F] [Finite F] (d : Cover F (ReeF4.Model m)),
        Nat.card d.toMonoidHom.ker = p →
          ∃ (P : Sylow p (ReeF4.Model m)) (s : P →* F),
            d.toMonoidHom.comp s = (P : Subgroup (ReeF4.Model m)).subtype)
    {G : Type u} [Group G] [Group.IsPerfect G]
    (hmodel : Triality.IsQTKETrialityModel G ∨ ReeF4.IsReeF4Model G ∨
      Nonempty (G ≃* Tits.ParrottGroup)) :
    (universalProjection G).ker = ⊥ :=
  universalProjection_ker_eq_bot_of_model_calculations htriality
    (fun m hm _ => ReeF4.CentralCovers.universalProjection_ker_eq_bot_of_prime_local_sections
      m hm (hreeTwo m hm) (hreeOdd m hm)) htits hmodel

end CFSG.Quasithin.ChapterI.LieMultipliers.Twisted
