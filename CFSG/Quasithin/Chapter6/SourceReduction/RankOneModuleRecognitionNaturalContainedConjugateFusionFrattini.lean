module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionDefs
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# Frattini reduction for the contained central line

The original Sylow normalizes Z_S, hence its intersection with C_G(Z_S)
is a Sylow subgroup of that centralizer. Frattini therefore puts N_G(Z_S)
inside the join of C_G(Z_S) with the normalizer of this intersection.
Under the contained-centralizer hypothesis, source 6.1.9(2) bounds both
factors by M. This supplies exactly the normalizer factorization used by
the conjugate-fusion argument; the 6.1.9(2) bound remains explicit.

Source: Aschbacher--Smith, 6.1.9(1,5), printed p.669 (PDF p.686).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- T normalizes Z, so its centralizer in T really is Sylow in C_G(Z).
In the contained branch, Frattini and 6.1.9(2) put N_G(Z) inside M. -/
theorem centralLineNormalizerFactorization_of_S_normalizer
    (h : Hypothesis611 κ T L M V n)
    (hI : centralizer (ZS (T : Subgroup G) L V : Set G) ≤ M)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M) :
    CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L V) := by
  let Z := ZS (T : Subgroup G) L V
  let I := centralizer (Z : Set G)
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    h.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer Z)
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  have hfr := le_normalizer_sylow_sup I (normalizer (Z : Set G))
    (centralizer_le_normalizer _) (normalizer_le_normalizer_centralizer Z) P
  rw [hP, subgroupOf_map_subtype] at hfr
  have hNM : normalizer (Z : Set G) ≤ M := hfr.trans (sup_le hNS hI)
  intro d hd
  exact ⟨1, one_mem _, d, ⟨hNM hd, hd⟩, (one_mul d).symm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
