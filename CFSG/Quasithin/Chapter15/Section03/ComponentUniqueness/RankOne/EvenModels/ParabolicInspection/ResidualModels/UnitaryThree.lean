module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.Data
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary

/-!
# The PSU₃ branch of the larger-field parabolic inspection

The genuine unitary matrix geometry in `RankOneBorels.Unitary` proves that
any proper overgroup of a Sylow two-subgroup lies in its normalizer. Its
proof uses Bruhat factorization and opposite-root generation in SU₃,
descends through SU₃ → PSU₃, and transports arbitrary Hermitian forms by
actual matrix conjugation. The parameter `2 ^ n` is the fixed-field order;
the matrix field has order `(2 ^ n) ^ 2`.

Apply that result to the supplied Sylow subgroup of L. Embedding its
normalizer in G gives exactly `L ∩ N_G(S ∩ L)`, the source Borel. The
quotient parabolic supplies the reverse containment, and the existing
component-action transport gives the literal equality in `I/C_I(L)`.
Neither an involution action nor a simplicity calculation is needed for
this rank-one step.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, printed p.1140, the paragraph beginning `Assume that n > 1`;
1.1.5(3)(a), pp.501--502; F.1.3(1), pp.259--260.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

/-- The actual upstairs intersection is the Sylow normalizer in the PSU₃ branch. -/
theorem unitaryThree_intersection {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) (hp : QuotientParabolic c) :
    M ⊓ L = borel L S := by
  obtain ⟨P, hP⟩ := component_sylow c
  have hf : RankOneSylowFacts P := by
    obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
    apply rankOneSylowFacts_of_equiv P e
    exact rankOneSylowFacts_psu3 J n hn hcard hconj _
  have hb := rankOneBorelFacts_of_sylow L S P hP hf
  have hproper : M ⊓ L < L :=
    lt_of_le_of_ne inf_le_right (fun he => c.component_outside (he ▸ inf_le_left))
  exact le_antisymm
    (hb.unique_maximal (M ⊓ L) (inf_le_inf_right L c.sylow_le_M) hproper)
    (borel_le_intersection c hp)

/-- The literal Borel equality in the component action quotient for PSU₃(2ⁿ). -/
theorem unitaryThree_residual_inspection {n : ℕ} (hn : 1 < n)
    (_hs : IsSimpleGroup L) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (hp : QuotientParabolic c) :
    c.toComponentAction.image M ⊓ c.toComponentAction.image L =
      borel (c.toComponentAction.image L) (c.toComponentAction.image S) :=
  quotient_intersection_eq_borel_of_intersection c
    (unitaryThree_intersection c (by omega) hm hp)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
