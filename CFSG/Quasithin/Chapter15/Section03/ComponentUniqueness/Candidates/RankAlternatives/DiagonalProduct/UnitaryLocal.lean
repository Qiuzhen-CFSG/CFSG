module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.UnitaryLocal.Placement
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.UnitaryLocal.BorelCubic
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary

/-!
# Exclusion of the unitary signed alternative

An order-three actor supplied by the signed alternative preserves the
Borel containing the image of M ∩ L in its specified quotient model.
The rank bound makes this Borel's three-part nontrivial. The concrete
`cubicBorelAction` theorem then makes the corresponding order-three
unitary Borel conjugation inner, contradicting the supplied outer action.

The conditional reduction is retained, and `unitary_exclusion` discharges
its matrix premise and supplies the unitary exclusion used in 15.3.37.
Its inputs are genuine earlier local conclusions: Sylow control, relative
component subnormality, noncontainment in M, the theta identity, the
three-group two-core quotient, the component orbit bound and the rank
bounds. The same field, Frobenius involution, quotient equivalence and
actor are retained throughout. No O_{2,Φ} quotient is replaced by O₂,
and no result from 15.3.38--40 is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of 15.3.37, printed p.1135.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.UnitaryLocal
variable {G : Type*} [Group G] [Finite G]

/-- The unitary exclusion reduced to its precise matrix Borel obligation.
The conclusion is not claimed without proving `hmodel`. The proof needs
only the quotient model already linked to the actor; an independent
identification of L itself is unnecessary. -/
theorem not_unitary_of_borel_action {Yplus S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSM : S ≤ M) (hθ : theta (M ⊓ I) = Yplus)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsSubnormal) (hLM : ¬ L ≤ M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (hYrank : primeRank 3 Yplus = 2) (hLrank : 1 ≤ primeRank 3 L)
    (hIrank : primeRank 3 I ≤ 2)
    {y : G} (hy : y ∈ Yplus) (hy3 : orderOf y = 3)
    {n : ℕ} (hn : 0 < n) (hmodel : CubicBorelAction n)
    (hact : UnitaryDiagonalOnTwoQuotient L y (2 ^ n)) : False := by
  obtain ⟨F, _, _, J, hcard, hconj, e, α, d, hc, ho, he⟩ := hact
  let H := BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite H := Finite.of_surjective e e.surjective
  let f : L →* H := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 L := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [map_eq_one_iff e e.injective]
    change x ∈ (QuotientGroup.mk' (pCore 2 L)).ker ↔ x ∈ pCore 2 L
    rw [QuotientGroup.ker_mk']
  obtain ⟨T, hT⟩ := component_sylow hLI hL P hP
  have hYM : Yplus ≤ M := by
    rw [← hθ]
    exact (Subgroup.closure_le _).mpr (fun _ hx => hx.1.1)
  have hne : componentPart Yplus L ≠ ⊥ :=
    ComponentIntersection.intersectionResidual_ne_bot_of_local_facts
      hI hθ hLI hindex hYrank hLrank hIrank
  have hB := rankOneSylowFacts_psu3 J n hn hcard hconj (T.mapSurjective hf)
  obtain ⟨hthree, hpres⟩ := local_borel_data hSM hYM hy hLM hY hne
    T hT α (J.unitaryConjHom d) f hf hker hc he hB
  exact ho (hmodel F J hcard hconj (T.mapSurjective hf) d hthree
    (compatible_cube α (J.unitaryConjHom d) f hf hc hy3 he) hpres)

/-- Exclude the unitary branch in the exact form required by
`rankTwoDiagonal_of_signed_of_core_cover`. The matrix premise of the
local reduction is now proved. The supplied quotient action already
identifies the relevant model, so the additional identification of L
itself need not be used. All normality assumptions remain relative to I. -/
theorem unitary_exclusion {Yplus S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSM : S ≤ M) (hθ : theta (M ⊓ I) = Yplus)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsSubnormal) (hLM : ¬ L ≤ M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (hYrank : primeRank 3 Yplus = 2) (hLrank : primeRank 3 L = 2)
    (hIrank : primeRank 3 I ≤ 2) :
    ∀ y ∈ Yplus, orderOf y = 3 →
      ∀ n : ℕ, 0 < n → 2 ^ n % 3 = 2 → ClassicalGroup.IsPSU L 3 (2 ^ n) →
        UnitaryDiagonalOnTwoQuotient L y (2 ^ n) → False := by
  intro y hy hy3 n hn hmod _ hact
  exact not_unitary_of_borel_action hI hSM hθ hY hLI hL hLM P hP hindex
    hYrank (by omega) hIrank hy hy3 hn (cubicBorelAction n hn hmod) hact

end CFSG.Quasithin.Chapter15.Section03.Candidates.UnitaryLocal
