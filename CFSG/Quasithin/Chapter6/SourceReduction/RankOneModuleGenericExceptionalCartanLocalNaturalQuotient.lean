module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalHermitian
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNaturalExclusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalInitial

/-!
# Excluding the natural central-quotient row

The natural row of 5.1.3 concerns [W,L]/C_[W,L](L), and does not supply
coordinates or a splitting of [W,L]. The existing
`IsNaturalFixedQuotient` retains the equivariant surjection whose kernel
is exactly the fixed subgroup.
The proved outside centralization makes this kernel trivial. Thus the
same map gives natural coordinates on the entire layer, which the
original escaping cubic excludes. Apply the same argument to the actual
omega-span at the unchanged Sylow choice and field degree.

This discharges the natural central-quotient alternative. The exhaustive
source alternative producer and the original component sieve remain open.
Source: Aschbacher--Smith 5.1.3(3), 5.1.13, pp.630--631,638,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The natural central-quotient row is excluded on both the original
module and its literal moved layer; the central kernel is proved zero. -/
theorem localCartan_not_natural_fixed_quotient
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) :
    (¬ IsNaturalFixedQuotient L W m) ∧
      (¬ IsNaturalFixedQuotient L (layer L W) m) := by
  have hHC := (residual_le_omegaCentralizer_iff hH.1.1.2).mp
    (d.residual_le.trans (localCartan_centralizes h hH hgen c hY d))
  have hn := localCartan_not_natural h hH hgen c hY d (m:=m)
  exact ⟨fun hm => hn.1 (hm.natural_of_fixed_eq_bot
      (h.reduced_fixed_eq_bot_of_outside_centralizes hH hHC)),
    fun hm => hn.2 (hm.natural_of_fixed_eq_bot
      (h.layer_fixed_eq_bot_of_outside_centralizes hH hHC))⟩

/-- In particular the natural central-quotient row on the source omega-span
is impossible. Reselection leaves the original Sylow and exponent unchanged. -/
theorem localCartan_not_natural_fixed_quotient_omega_span
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) :
    ¬ IsNaturalFixedQuotient L
      (layer L (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)) m :=
  (localCartan_not_natural_fixed_quotient
    (localCartan_omega_span_input h hH hgen c hY d) hH hgen c hY d).2

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
