module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Primitive
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Fitting
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Alternatives
public import CFSG.Quasithin.Chapter14.Section06.SourcePrimitiveOddResidual

/-!
# The primitive residual in the actual generalized-Fitting preimage

The earlier H=PT reduction supplies an elementary minimal normal odd
residual in H/O₂(H); 14.6.12 supplies its order p². Its actual iterated
quotient action is irreducible, hence O²(H) belongs to Ξ. Apply the
normal-or-component detection theorem inside the chosen Mc. Both branches
place the residual, and therefore its Mc-normal closure, in O₂,F*(Mc).

This proves the precise containment used by the first paragraph of
14.6.17 independently of the remaining model classification in 14.6.14.
The primitive and exchanged-factor inputs are earlier source statements,
owned by qt-e-14612-singleton and qt-e-quintic-recognition. The companion
minimal-solvable application constructs the primitive input from the
already proved reduction, on the same H.

Source: Aschbacher--Smith, pp.1030--1033 and 1035--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))

include hG hempty hM hunique hmany hcard e hab hH

/-- The precise Fitting containment required by original 14.6.17.
No maximal-prime choice, suitability, U3 or model conclusion is needed. -/
theorem source_residualClosure_le_fittingPreimage
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    residualClosure H Mc ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc := by
  have hp : p.Prime := by rcases d.prime with h | h <;> rw [h] <;> decide
  have ho : Odd p := by rcases d.prime with h | h <;> rw [h] <;> decide
  let : Fact p.Prime := ⟨hp⟩
  have hXi := residual_mem_Xi T H hH.1.2 hH.1.1 ho hprim d.residual_card
  have hF := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hHC : H ≤ centralizer (centralInvolutions T : Set G) :=
    hF.H_centralizes
  have hHMc : H ≤ Mc := hHC.trans (InitialSource.centralizer_le_partner T hunique)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hunique.symm ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  have hSylow : Chapter1.IsSylowIn 2 (T : Subgroup G) Mc := by
    refine ⟨T.subtype hTMc,?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]
  obtain ⟨q,hq,hoq,hQ⟩ := hXi.odd_quotient
  let : Fact q.Prime := ⟨hq⟩
  let P : Sylow q (residual H) := default
  have hi := Chapter1.XiEmbedding.localInput_of_mem_Xi hXi hSylow
    (sup_le ((residual_le H).trans hHMc) hTMc) hoq hQ P
  exact localInput_closure_le_fittingPreimage hi (hG.twoLocal_sqtk hMc.1.1) hSylow

/-- The original residual, rather than a replacement model subgroup,
lies in the actual Mc generalized-Fitting preimage. -/
theorem source_residual_le_fittingPreimage
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    residual H ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc :=
  (le_conjugateSpanBy _ _).trans
    (source_residualClosure_le_fittingPreimage hG T hempty hM hunique hmany hcard e hab
      H hH a p H0 H1 H2 hprim d)

omit hH in
/-- Construct the primitive input for the actual minimal solvable outside
subgroup; the order p² identifies its prime with the exchanged-factor prime. -/
theorem source_primitiveResidual_of_minimal_solvable
    (hminimal : H ∈ Chapter3.HStar (T : Subgroup G) M) (hs : Group.IsSolvable H)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) : PrimitiveResidual H p := by
  obtain ⟨q,hq,hE,_hr,_hne,hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hunique hmany hcard e hab H hminimal hs
  let := hE
  have hqp : q.Prime := by rcases hq with h | h <;> rw [h] <;> decide
  have hpp : p.Prime := by rcases d.prime with h | h <;> rw [h] <;> decide
  let : Fact q.Prime := ⟨hqp⟩
  have heq : q = p := by
    rcases (IsElementaryAbelian.isPGroup q (pResidual 2 (H ⧸ pCore 2 H))).card_eq_or_dvd with h | h
    · rw [d.residual_card] at h
      have hlarge := hpp.two_le
      nlinarith
    · rw [d.residual_card] at h
      exact Nat.prime_eq_prime_of_dvd_pow hqp hpp h
  subst q
  exact ⟨hE,hmin⟩

/-- The minimal-solvable source application discharges the primitive premise
on the same H; only the earlier exchanged factors remain explicit. -/
theorem source_minimal_solvable_residual_le_fittingPreimage
    (hminimal : H ∈ Chapter3.HStar (T : Subgroup G) M) (hs : Group.IsSolvable H)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    residual H ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc :=
  source_residual_le_fittingPreimage hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2
    (source_primitiveResidual_of_minimal_solvable hG T hempty hM hunique hmany hcard e hab
      H a hminimal hs p H0 H1 H2 d) d

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
