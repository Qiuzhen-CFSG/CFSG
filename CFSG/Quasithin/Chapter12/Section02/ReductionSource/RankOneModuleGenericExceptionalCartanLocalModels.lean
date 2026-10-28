module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Local Cartan containing quotients on the original Chapter 12 module

Apply the universal source reductions to the whole reduced subgroup. The
seed remains proper in the containing two-core image, with the rank-one
and small alternating containers excluded. The original quotient actor
retains a full Sylow in its induced action group, permutability, solvability
and escape of the literal residual image. These are reductions of the local
sieve; its remaining classification and module arguments are not assumed.

Source: Aschbacher--Smith 5.1.12--13 and 12.2.2, printed pp.635--638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- Apply the universal local sieve reduction to the original whole reduced subgroup. -/
theorem rankOne_local_cartan_containing_quotient_restrictions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ ClassificationModels.IsBenderModel (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m)) ∧
        ¬ (IsAlternating (C ⧸ pCore 2 C) 5 ∨ IsAlternating (C ⧸ pCore 2 C) 6 ∨
          IsAlternatingCover (C ⧸ pCore 2 C) 6) :=
  localCartan_escape_containing_quotient_restrictions
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

/-- Apply the universal local sieve reduction to the original whole reduced subgroup. -/
theorem rankOne_local_cartan_escaping_sylow_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ C : Subgroup Y, C.IsCComponent ∧
      residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
      ∃ hn : ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal,
        let J := (componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y
        letI : J.Normal := hn
        let f := normalQuotientAction J (pCore 2 J)
        let Dbar := (A.subgroupOf Y).map f
        let Bbar := (B.subgroupOf Y).map f
        let Tbar := ((T : Subgroup G).subgroupOf Y).map f
        Chapter1.IsSylowIn 2 Tbar f.range ∧
          (Dbar : Set (MulAut (J ⧸ pCore 2 J))) * (Tbar : Set _) =
            (Tbar : Set _) * (Dbar : Set _) ∧
          Group.IsSolvable (Dbar ⊔ Tbar : Subgroup _) ∧
          IsCyclic Dbar ∧ Odd (Nat.card Dbar) ∧
          Bbar ≤ normalizer (Dbar : Set (MulAut (J ⧸ pCore 2 J))) ∧
          ¬ Dbar ≤ normalizer (((residual H).subgroupOf Y).map f : Set _) ∧
          Dbar ≠ ⊥ ∧ ¬ Dbar ≤ Bbar :=
  localCartan_exists_escaping_sylow_action
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
