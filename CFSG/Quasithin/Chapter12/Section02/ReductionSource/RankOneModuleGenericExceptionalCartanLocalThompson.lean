module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original Chapter 12 left Thompson comparison

The universal input adapter retains the chosen reduced module and the
original Sylow. In the noncentral A₇ configuration, the actual left FF
classification either puts J(T) in (T∩L)O₂(LT), normalized by the Borel,
or marks L/O₂(L) as A₅ and proves degree two. At larger degree the original
Hall Cartan and witnessed escaping cubic both normalize J(T). The five
row instead makes the original cubic fail to normalize J(T). The final
application uses the completed FF reduction on the original inputs.

Source: Aschbacher–Smith 5.1.13, printed p.637, applied in 12.2.2, p.795.
The block exclusions and unconditional Cartan escape remain with the
local Cartan classification owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C K : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The actual left quotient is recognized in the non-natural alternative. -/
theorem rankOne_local_cartan_left_thompson_comparison
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (a : LocalA7Configuration T L H X K) :
    (Chapter6.Source.RankOneGeneric.localBorel T L ⊔ (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∨
      (n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :=
  a.left_thompson_comparison
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)

/-- At larger degree, the literal source Cartan and escaping cubic normalize
J(T); its original two-core containment is retained. -/
theorem rankOne_local_cartan_cubic_normalizes_thompson
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 2 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (a : LocalA7Configuration T L H X K)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X C) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      A ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      C ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
  a.cartan_and_cubic_normalize_thompson
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by omega) hpsl) c d hn


/-- The original escaping cubic distinguishes the two genuine left FF rows;
the symmetric-five row also identifies the entire left Hall Cartan. -/
theorem rankOne_local_cartan_thompson_cubic_dichotomy
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (a : LocalA7Configuration T L H X K)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X C) :
    (elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter6.Source.RankOneGeneric.localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∨
    (n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
      A = C ∧ ¬ C ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :=
  a.left_thompson_cubic_dichotomy
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) c d

/-- The left comparison applied after the genuine FF reduction, using only
the original Chapter 12 inputs and the witnessed noncentral component. -/
theorem rankOne_local_cartan_noncentral_left_thompson_dichotomy
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T) :
    (elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter6.Source.RankOneGeneric.localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∨
    (n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
      A = C ∧ ¬ C ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :=
  localCartan_noncentral_left_thompson_dichotomy
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
