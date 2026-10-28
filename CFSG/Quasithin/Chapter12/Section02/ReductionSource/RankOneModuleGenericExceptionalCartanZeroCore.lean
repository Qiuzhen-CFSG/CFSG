module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreTriality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLinearFour

/-!+# The literal zero-core prime pair in the chosen-module argument

The original source construction now feeds the exact prime-index, mixed
solvability and faithful local-Sylow calculations. In a parabolically marked
binary-triality row, the selected factor itself has quotient PSL₂(8), the
actor is cubic, and the original B ∩ R has order seven. The fixed-module
comparison uses the original left degree, without identifying it with three.

Recognition of the marked model, the subsequent zero-core exclusion and
the remaining field and changed-Sylow arguments stay with
qt-d-1222-rankone-cartan-local-to-global. This does not assert normalization.
Source: Aschbacher–Smith, 5.2.2 and 12.2.2, printed pp.647–648,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- The selected prime pair has the literal zero-core geometry used in the
model sieve, with the local-construction premise fully discharged. -/
theorem rankOne_cartan_source_zeroCore_geometry
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧
      ((generated L H D R).pCoreIn 2 = ⊥ →
        let S := Global.sourceS L H
        ((D ⊔ S) ⊔ (B ⊓ R)) ⊓ (R ⊔ S) = S ⊔ (B ⊓ R) ∧
        (S ⊔ (B ⊓ R)).relIndex ((D ⊔ S) ⊔ (B ⊓ R)) = p ∧
        Group.IsSolvable ((D ⊔ S) ⊔ (B ⊓ R) : Subgroup G) ∧
        ¬ Group.IsSolvable (R ⊔ S : Subgroup G) ∧
        (solvableResidual (R ⊔ S : Subgroup G)).map (R ⊔ S : Subgroup G).subtype = R ∧
        Chapter1.IsSylowIn 2 S ((D ⊔ S) ⊔ (B ⊓ R)) ∧
        Chapter1.IsSylowIn 2 S (R ⊔ S) ∧
        ∀ N : Subgroup G, N ≤ S ⊔ (B ⊓ R) →
          (D ⊔ S) ⊔ (B ⊓ R) ≤ normalizer (N : Set G) →
          R ⊔ S ≤ normalizer (N : Set G) → N = ⊥) := by
  let hi := M.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨R,d⟩ := source_prime_pair hi hH hpar hthree c hd
  refine ⟨R,d,?_⟩
  intro hz
  obtain ⟨hs,hnsol⟩ := d.zeroCore_mixed_solvability hi hH c hd hz
  exact ⟨d.zeroCore_parabolic_intersection hi hH c hd hz,
    d.zeroCore_left_index hi hH c hd hz,hs,hnsol,
    d.zeroCore_right_residual hi hH c hd hz,
    d.zeroCore_sylows_and_faithfulness hi hH c hd hz⟩

/-- An actual binary-triality parabolic marking gives the original selected
PSL₂(8) section and seven-actor fixed-module comparison. -/
theorem rankOne_cartan_zeroCore_binaryTriality
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hsmall : n = 2 ∨ n = 4 ∨ n = 8)
    {R : Subgroup G} (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      binaryTrialityPrimeAmalgam) :
    p = 3 ∧ Global.sourceS L H ≤ R ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧
      Nat.card (B ⊓ R : Subgroup G) = 7 ∧
      ((B ⊓ R : Subgroup G) ≤ centralizer
        (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G) ↔
        (B ⊓ R : Subgroup G) ≤ omegaCentralizer T) :=
  d.zeroCore_binaryTriality_seven_fixed (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH c hd hsmall hz e

/-- Transport the literal selected quotient through a right-parabolic marking;
the representative equation retains the original inclusion into RS. -/
theorem rankOne_cartan_zeroCore_right_quotient
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {R : Subgroup G} (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    {X : Type*} [Group X] (e : (R ⊔ Global.sourceS L H : Subgroup G) ≃* X) :
    ∃ f : (R ⧸ pCore 2 R) ≃* (solvableResidual X ⧸ pCore 2 (solvableResidual X)),
      ∀ x : R, ∃ y : solvableResidual X,
        (y : X) = e (inclusion (show R ≤ R ⊔ Global.sourceS L H from le_sup_left) x) ∧
        f (QuotientGroup.mk' (pCore 2 R) x) =
          QuotientGroup.mk' (pCore 2 (solvableResidual X)) y :=
  d.zeroCore_right_quotient_transport (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH c hd hz e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
