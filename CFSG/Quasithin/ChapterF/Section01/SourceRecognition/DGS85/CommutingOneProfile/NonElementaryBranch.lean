module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryBranch

/-!
# The terminal Suzuki order obstruction

The Chapter 11 seed count gives |V| = qα² qβ. Thus the upper bound on
the beta core in the Suzuki candidate of (11.8) forces Qβ = V. The earlier
commutator bound then puts Φ(Qα) in Qβ and makes the literal S/Qβ elementary,
contrary to the branch hypothesis.

The seed geometry, the Suzuki order bound, and the earlier commutator bound
are still explicit inputs. This completes their terminal implication only;
it does not classify the local quotient or prove the unitary profile.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
proof of (11.8), printed p.176.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

/-- The Suzuki candidate's upper bound identifies the core with the actual
pair span; no separate equality or full-size assumption on the span is needed. -/
theorem beta_core_eq_pairSpan_of_small_order
    {P : Type*} [Group P] [Finite P] (Zα Zα₂ : Subgroup P)
    (g : P) (hconj : Zα.map (MulAut.conj g).toMonoidHom = Zα₂)
    (hn : pCore 2 P ≤ normalizer (Zα : Set P))
    (qα qβ : ℕ) (hqβ : 0 < qβ)
    (hZ : Nat.card Zα = qα * qβ ^ 2)
    (hindex : (Zα ⊓ pCore 2 P).relIndex Zα = qβ)
    (hinter : Nat.card ((Zα ⊓ pCore 2 P) ⊓ (Zα₂ ⊓ pCore 2 P) : Subgroup P) = qβ)
    (hsmall : Nat.card (pCore 2 P) ≤ qα ^ 2 * qβ) :
    pCore 2 P = pairSpan Zα Zα₂ (pCore 2 P) := by
  have hpair := (pairSpan_card_of_seed_index (pCore 2 P) Zα Zα₂ g
    (Normal.map_conj_eq (pCore 2 P) g) hconj hn qα qβ hqβ hZ hindex hinter).2
  exact (eq_of_le_of_card_ge (pairSpan_le_core Zα Zα₂ (pCore 2 P))
    (hsmall.trans hpair.ge)).symm

/-- The terminal Suzuki contradiction, with the pair/core identity discharged
by the earlier order comparison. This retains S/Qβ, the original core and
relative centralizer, and the earlier local commutator bound. -/
theorem nonElementary_beta_excludes_small_core
    {P : Type*} [Group P] [Finite P]
    (Qα Zα Zα₂ S : Subgroup P) [IsElementaryAbelian 2 Zα]
    (g : P) (hconj : Zα.map (MulAut.conj g).toMonoidHom = Zα₂)
    (hQα : IsPGroup 2 Qα) (hS : S = Qα ⊔ pCore 2 P)
    (hn : pCore 2 P ≤ normalizer (Zα : Set P))
    (qα qβ : ℕ) (hqβ : 0 < qβ)
    (hZ : Nat.card Zα = qα * qβ ^ 2)
    (hindex : (Zα ⊓ pCore 2 P).relIndex Zα = qβ)
    (hinter : Nat.card ((Zα ⊓ pCore 2 P) ⊓ (Zα₂ ⊓ pCore 2 P) : Subgroup P) = qβ)
    (hsmall : Nat.card (pCore 2 P) ≤ qα ^ 2 * qβ)
    (hcomm : ⁅Qα,pairSpan Zα Zα₂ (pCore 2 P)⁆ ≤ Zα)
    (hcentral : Qα ≤ centralizer (Zα : Set P))
    (hself : centralizer (pCore 2 P : Set P) ≤ pCore 2 P)
    (hne : ¬ IsElementaryAbelian 2 (S ⧸ (pCore 2 P).subgroupOf S)) : False := by
  have hpair := beta_core_eq_pairSpan_of_small_order Zα Zα₂ g hconj hn
    qα qβ hqβ hZ hindex hinter hsmall
  exact nonElementary_beta_excludes_pairSpan_core Qα (pCore 2 P) Zα Zα₂ S
    hQα hS le_normalizer_of_normal hpair hcomm hcentral (inf_le_right.trans hself) hne

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
