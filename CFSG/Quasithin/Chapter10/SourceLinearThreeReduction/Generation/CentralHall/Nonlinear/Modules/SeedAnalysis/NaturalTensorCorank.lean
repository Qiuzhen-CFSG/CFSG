module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorAmbient
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCompleteBound
public import CFSG.Quasithin.Chapter10.SourceWeakClosure

/-!
# Ambient corank in the original nonseparated natural-tensor branch

The original maximal-local uniqueness and full-module construction supply
E.6.1. The full automizer's displacement bound gives m >= n >= 3, so the
proved E.6.3 yields r(G,V_M) >= n. Consequently the ambient centralizer of
any subgroup of V_M of corank below n lies in the original M.

The final Hall alternative retains the actual quotient kernel, both factor
markings, original seed representation and determinant field action alongside
these full-module bounds. All seed stability needed for small displacement
was proved; no equality of the seed and full module is assumed. The higher
Thompson, generation and Cartan steps of 9.2.4--7 still remain before the
ambient tensor can be excluded and SourceNonnormalCentralHallAt assembled.
Source: Aschbacher--Smith 9.2.3, printed p.730, using E.6.3, p.245;
10.1.1--2 and10.2.3, pp.741--742,745, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
open Representation.BinaryOffender.NaturalTensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The original full module satisfies E.6.1, with its actual maximal local subgroup. -/
theorem original_full_hypothesisE61 :
    ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T D.maximalLocal D.fullModule := by
  have hu := D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_sup_right.trans hu.2.1
  have hVN := D.maximalLocal_normalizes_fullModule
  have hVT := D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)
  refine ⟨D.simpleQTKE,hu.1,hTM,?_,inferInstance,hVT,
    (normal_subgroupOf_iff_le_normalizer hVT).mpr (hTM.trans hVN),?_,?_⟩
  · intro he
    exact D.module_ne_bot (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans_eq he))
  · intro g hg
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hVN hg))
  · intro N hN hle
    apply hu.2.2 N hN
    apply le_trans _ hle
    exact le_inf (le_inf hu.2.1 (hu.2.1.trans hVN))
      (source_join_normalizes_full_sylow_centralizer D (source_module_nonsolvable_uniqueness D))

/-- Source 9.2.3's lower bound on the actual full module, without a seed-stability premise. -/
theorem original_even_full_globalR_ge
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    (n : ℕ∞) ≤ ChapterE.globalR D.fullModule := by
  have hm := original_even_full_localM_ge D c n hn e ht htn hsep
  have hh := ChapterE.Section06.FrobeniusReduction.lower_bound_knownSimple
    (original_full_hypothesisE61 D) (by omega : 2 < ChapterE.localM D.fullModule)
  exact (ENat.natCast_le_natCast.mpr hm).trans hh.1

/-- Actual centralizer control for every original full-module subgroup below the corank bound. -/
theorem original_even_full_small_corank_centralizer
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    {U : Subgroup G} (hU : U ≤ D.fullModule)
    (hsmall : ChapterE.subgroupCorank D.fullModule U < n) :
    centralizer (U : Set G) ≤ D.maximalLocal := by
  apply le_trans _ (source_fullModule_normalizer D).le
  exact ChapterE.centralizer_le_normalizer_of_corank_lt_globalR hU
    ((ENat.natCast_lt_natCast.mpr hsmall).trans_le
      (original_even_full_globalR_ge D c n hn e ht htn hsep))

/-- The literal Hall alternative with its original markings and ambient full-module bounds. -/
theorem original_hall_conclusion_or_natural_tensor_ambient
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
            D.seed ≤ centralizer (L : Set G)) ∧
          OriginalEvenNaturalTensorAnalysis D ht n e ∧
          OriginalEvenSeedDeterminantCoordinates D ht n e ∧
          n ≤ ChapterE.moduleM (normalizerRepresentation (originalSeedAction D)) ∧
          (∀ a : linearNormalizer (originalSeedAction D), a ≠ 1 →
            n ≤ operatorFixedCodim (normalizerRepresentation (originalSeedAction D) a)) ∧
          (∀ a : ChapterE.Automizer D.fullModule, a ≠ 1 →
            n ≤ operatorFixedCodim (ChapterE.automizerRepresentation D.fullModule a)) ∧
          n ≤ ChapterE.localM D.fullModule ∧
          (n : ℕ∞) ≤ ChapterE.globalR D.fullModule ∧
          (∀ U : Subgroup G, U ≤ D.fullModule → ChapterE.subgroupCorank D.fullModule U < n →
            centralizer (U : Set G) ≤ D.maximalLocal) := by
  rcases original_hall_conclusion_or_natural_tensor_displacement D c with hh |
      ⟨t,ht,htn,n,hn,e,hs,ha,hdet,hm,hdisp⟩
  · exact Or.inl hh
  · exact Or.inr ⟨t,ht,htn,n,hn,e,hs,ha,hdet,hm,hdisp,
      original_even_automizer_displacement_ge D c n hn e ht htn hs,
      original_even_full_localM_ge D c n hn e ht htn hs,
      original_even_full_globalR_ge D c n hn e ht htn hs,
      fun _ hU hsmall => original_even_full_small_corank_centralizer D c n hn e ht htn hs hU hsmall⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
