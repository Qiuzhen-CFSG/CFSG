module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Actor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Flags
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Pair
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Kernel
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Coordinates

/-!
# Barred parabolic marking for the five-dimensional branch

From the actual original natural L-module coordinates we construct a faithful
six-letter action of LT/C_LT(V), retaining its full conjugation formula and
surjective alternating restriction. The order-two flag gives an actual duad;
the residual/Sylow calculation identifies its stabilizer with the image of
L₁T. The resulting coset equivalence has fifteen points and intertwines the
literal coset action. The A₆ quotient L/O₂(L) also puts C_LT(V) inside T.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6(5), p.948, with Notation 12.2.5(2), p.796; Notations 13.2.1 and
13.3.3, pp.877,885; and 13.5.2–3 and 13.7, pp.915–916,935.

This is a conditional construction, not yet the source applicability theorem.
The original coordinates and standing flag facts must still be obtained by
applying the exact earlier source statements. The independent parabolic task
supplies the A₆ quotient. Neither the original four-space nor its action is
identified with the separate five-dimensional K* cover. The retained
`NaturalCoordinates.conjugation` formula is directly usable by
`FiveSeed.V_generated_by_flag`.

`Coordinates` identifies the faithful L-quotient and retains an explicit
automorphism comparing its natural action with the supplied L/O₂(L)
marking. It also derives the order-two flag from its dimension-one source
condition. No assumption equating the original V-action with the separate
K*-action on the cover is introduced.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking
open BinaryPermutation
variable {G : Type*} [Group G]
open BinaryPermutation.SixPairsQuadratic

/-- Construction of the source barred marking and kernel placement from the
original natural-module coordinates. The residual is the one in 13.3.3;
its agreement with 13.2.1 is proved, not assumed. -/
theorem barred_marking_of_natural_coordinates [Finite G]
    (L V V₁ L₁ : Subgroup G) (T : Sylow 2 G) [IsElementaryAbelian 2 V]
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hPV : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G))
    (hV₁V : V₁ ≤ V) (hV₁ : Nat.card V₁ = 2)
    (hTV₁ : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hL₁ : L₁ = (pResidual 2 ↥(L ⊓ normalizer (V₁ : Set G))).map
      (L ⊓ normalizer (V₁ : Set G)).subtype)
    (c : NaturalCoordinates L V (le_sup_left.trans hPV))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    let P := L ⊔ (T : Subgroup G)
    let N := actorKernel P V
    letI := actorKernel_normal P V hPV
    centralizer (V : Set G) ⊓ P ≤ (T : Subgroup G) ∧
      ∃ f : (P ⧸ N) →* Equiv.Perm (Fin 6),
        Function.Injective f ∧
        (∀ g : alternatingGroup (Fin 6), ∃ a, f a = g.val) ∧
        (∀ l : L, f (QuotientGroup.mk' N (inclusion le_sup_left l)) = (c.action l).val) ∧
        (∀ (p : P) (v : Additive V),
          c.equiv (conjugationRepresentation P V hPV p v) =
            naturalRepresentation (Fin 6) (f (QuotientGroup.mk' N p)) (c.equiv v)) ∧
        ∃ s : Pair,
          (∀ a : P ⧸ N,
            a ∈ ((L₁ ⊔ (T : Subgroup G)).subgroupOf P).map (QuotientGroup.mk' N) ↔
              pairPerm (f a) s = s) ∧
          ∃ E : ((P ⧸ N) ⧸ ((L₁ ⊔ (T : Subgroup G)).subgroupOf P).map
              (QuotientGroup.mk' N)) ≃ Pair,
            (∀ a, E (QuotientGroup.mk a) = pairPerm (f a) s) ∧
            (∀ a q, E (a • q) = pairPerm (f a) (E q)) := by
  let P := L ⊔ (T : Subgroup G)
  let N := actorKernel P V
  let := actorKernel_normal P V hPV
  obtain ⟨f, hfL, hact, hker⟩ := natural_extension P L V le_sup_left
    (sup_le L.le_normalizer hTL) hPV c.action c.surjective c.equiv
    (fun l v => c.conjugation l v.toMul)
  have hR : L₁ ⊔ (T : Subgroup G) = P ⊓ normalizer (V₁ : Set G) := by
    rw [hL₁, ← normalizer_residual_eq L V₁ (T : Subgroup G) T.isPGroup' hTL]
    exact residual_normalizer_sup_sylow P V₁ T le_sup_right hTV₁
  obtain ⟨s, hs⟩ := exists_pair_of_flag P V V₁ hPV hV₁V hV₁ c.equiv f hact
  let F := barHom P V hPV f hker
  have hF : ∀ g : alternatingGroup (Fin 6), ∃ a, F a = g.val := by
    intro g
    obtain ⟨l, rfl⟩ := c.surjective g
    exact ⟨QuotientGroup.mk' N (inclusion le_sup_left l), hfL l⟩
  have hS := bar_pair_stabilizer P V V₁ (L₁ ⊔ (T : Subgroup G)) hPV hV₁V hR f hker s hs
  refine ⟨centralizer_le_sylow_of_natural_action L V T hTL f hker
    c.action c.surjective hfL eL, F, barHom_injective P V hPV f hker, hF,
    hfL, hact, s, hS, pairCosets F hF _ s hS, ?_, ?_⟩
  · exact pairCosets_mk F hF _ s hS
  · exact pairCosets_equivariant F hF _ s hS

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking

end
