module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryCubic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryInvolution

/-!+# The ambient cubic and component exclusions on the Chapter 12 layer

The odd escaping configuration supplies n = 2 from the two intersecting
hyperplanes. A cubic in the original L normalizes T ∩ L and Z_S. Its image
in N_G(Z_S)/O₂(N_G(Z_S)) still has order three and lies outside the image
of C_G(Z_S). The original conjugation on Z_S descends to this quotient,
with precisely that centralizer image as its kernel.

Every perfect component lies in this kernel, since Aut(Z_S) is solvable.
The ambient cubic and rank-two bound therefore exclude the large binary
and alternating component models by A.3.18, including the triple covers.
All quotients here are of the actual normalizer of the original Z_S.

The identification of the W/Z_S transvection factors with lifted components,
their assembly, the amalgam contradiction, initial 6.1.4–5 and unconditional
6.1.27 remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, pp.674–675, and A.3.18, pp.51–53.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original cubic survives outside the centralizer image in the literal
normalizer quotient; its action is the original conjugation on Z_S. -/
theorem source_escape_ambient_cubic_of_abelian
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    n = 2 ∧
      let Z := ZS (T : Subgroup G) L (wholeReduced T L)
      let N := Escape.H (T : Subgroup G) L (wholeReduced T L)
      let I := (Escape.I (T : Subgroup G) L (wholeReduced T L)).subgroupOf N
      let q := QuotientGroup.mk' (pCore 2 N)
      pCore 2 N ≤ I ∧ primeRank 3 (N ⧸ pCore 2 N) ≤ 2 ∧
      (∃ c : N, (c : G) ∈ L ∧ (c : G) ∈ normalizer ((T : Subgroup G) ⊓ L : Set G) ∧
        orderOf c = 3 ∧ orderOf (q c) = 3 ∧ q c ∉ I.map q) ∧
      ∃ α : (N ⧸ pCore 2 N) →* MulAut Z,
        (∀ (c : N) (z : Z), (α (q c) z : G) = (c : G) * z * (c : G)⁻¹) ∧
        α.ker = I.map q ∧ Group.IsSolvable (MulAut Z) := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  have hn := (d.parameter_and_intersection h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611)).1
  subst n
  obtain ⟨hc,hr,hd⟩ := natural_four_ambient_quotient_cubic h611 hnatural
  exact ⟨rfl,hc,hr,hd,natural_four_quotient_line_action h611 hnatural⟩

/-- The ambient source data supply the component exclusions, without an
assumed rank bound or centralizer containment for the component. -/
theorem source_escape_ambient_component_sieve_of_abelian
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    n = 2 ∧
      let N := Escape.H (T : Subgroup G) L (wholeReduced T L)
      let I := (Escape.I (T : Subgroup G) L (wholeReduced T L)).subgroupOf N
      let q := QuotientGroup.mk' (pCore 2 N)
      ∀ K : Subgroup (N ⧸ pCore 2 N), IsComponent _ K →
        K ≤ I.map q ∧
        (Nat.Coprime 3 (Nat.card (center K)) →
          IsPGroup 2 (MulAut.Outer (K ⧸ center K)) → primeRank 3 K ≤ 1) ∧
        (∀ m, 6 ≤ m → ¬ Chapter1.Section02.LocalModels.IsAlternating K m) ∧
        ¬ (Chapter1.Section02.LocalModels.IsAlternatingCover K 6 ∨
          Chapter1.Section02.LocalModels.IsAlternatingCover K 7) ∧
        (∀ m, m = 4 ∨ m = 5 →
          ¬ Nonempty (K ≃* BinaryLinear.OuterCyclic.LinearGroup m)) ∧
        (Nat.Coprime 3 (Nat.card (center K)) → ∀ m, m = 4 ∨ m = 5 →
          ¬ Nonempty ((K ⧸ center K) ≃* BinaryLinear.OuterCyclic.LinearGroup m)) := by
  have hn := (source_escape_ambient_cubic_of_abelian D h h611 hnatural hI hab).1
  subst n
  refine ⟨rfl,?_⟩
  dsimp only
  intro K hK
  let := hK.2
  exact ⟨natural_four_quotient_perfect_le_centralizer h611 hnatural K,
    natural_four_quotient_component_rank h611 hnatural K hK,
    fun _ hm => natural_four_quotient_component_not_alternating h611 hnatural K hK hm,
    natural_four_quotient_component_not_alternating_cover h611 hnatural K hK,
    fun _ hm => natural_four_quotient_component_not_binary_large h611 hnatural K hK hm,
    fun hz _ hm => natural_four_quotient_component_not_binary_cover h611 hnatural K hK hz hm⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
