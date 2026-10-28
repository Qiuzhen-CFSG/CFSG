module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.RankReduction.NaturalSolvable
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.Residual
/-!
# Reduction 13.3.14(b) from the original earlier hypotheses

The genuine 12.2.3 source and structural 12.2.2 theorem provide the chosen
module's TI property and normalizer placement. Source 1.2.7 supplies the
unique maximal local group from Theorems A and C; the original C-component
property supplies perfectness. These discharge the geometric/normalizer
premises of NaturalSolvable. The same result makes every rank-two odd
star residual move the original conjugate span, as required in (d).

Structural1222 remains with its earlier source owner; point escape is
13.3.6 and the cubic plane actor comes from the original marked parabolic.
No conclusion of reduction (b) or (d) is an input. Theorems A and C have
completed full-catalogue producers and can be instantiated by the assembly.
Source: Aschbacher–Smith, printed pp.891–892.
-/
@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
/-- The literal reduction (b), with all TI and normalizer conclusions derived from their source producer. -/
theorem natural_reduction_b_of_earlier_source
    (hA : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple D)
    (hC : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple D)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Chapter12.Section02.Structural1222.{u} KnownSimple.IsKnownSimple)
    (hescape : ¬ H ≤ M)
    (X : Subgroup G) (hXL : X ≤ L)
    (hx : letI := Section05.AmbientSource.source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map
        (Section05.AmbientSource.planeAction E)) = 3) :
    let Y := centralizingResidual (conjugateSpanBy U H)
    Group.IsSolvable Y ∧ ∀ p : ℕ, p.Prime → Odd p → primeRank p Y ≤ 1 := by
  let : Group.IsPerfect (L.subgroupOf (L ⊔ (T : Subgroup G))) :=
    d.counterexample.local_component.1.1.perfect
  let e : (L.subgroupOf (L ⊔ (T : Subgroup G))) ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply natural_residual_solvable_and_odd_rank d (h.source_chosen_TI structural d.chosen)
    (h.source_chosen_normalizer_le structural hA hC d.chosen) ?_ hescape X hXL hx
  intro N hN hLN
  exact (h.source_normalizer_maximal_unique structural hA hC).2 N hN hLN |>.trans d.local_normalizer.symm

/-- The actual odd residual preimage in (d) moves the original span; its
quotient, core and projection are those of G₁. -/
theorem natural_starResidual_moves_of_earlier_source
    (hA : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple D)
    (hC : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple D)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Chapter12.Section02.Structural1222.{u} KnownSimple.IsKnownSimple)
    (hescape : ¬ H ≤ M)
    (X : Subgroup G) (hXL : X ≤ L)
    (hx : letI := Section05.AmbientSource.source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map
        (Section05.AmbientSource.planeAction E)) = 3)
    (D : Subgroup (Star H)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hD : IsPGroup p D) (hr : 1 < primeRank p D) :
    ⁅conjugateSpanBy U H,(starResidual H D).map H.subtype⁆ ≠ ⊥ :=
  starResidual_moves_of_rank H (conjugateSpanBy U H) D hp hD hr
    ((natural_reduction_b_of_earlier_source d hA hC h structural hescape X hXL hx).2
      p Fact.out hp)

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
