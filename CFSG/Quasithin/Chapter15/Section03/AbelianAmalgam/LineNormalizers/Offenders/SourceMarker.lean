module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceMarker.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceMarker.NormalizerControl
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceMarker.Orbit

/-!
# Construction of the source marker for 15.3.67

The marker is the literal first projection of original V through the paired
quotient. The coordinate, orbit and normalizer arguments prove all six Facts
fields from OriginalData and the preceding original local conclusions.
In particular pointwise fixation derives displacement in E and hence
normalization of V. No terminal S₃, index-three, extra V-stability or splitting
hypothesis enters this construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154 (PDF pp.1170–1171).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer BestReduction.SourceAssembly
universe u
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)
  (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))
local notation "H" => temporaryLineNormalizer T V E
local notation "Q" => localCore T V E
local notation "S" => centralizerSylow T V E
local notation "J" => elementaryAbelianMaxJ S
local notation "q" => QuotientGroup.mk' Q
local notation "I" => thompsonImage T V E
local notation "σ" => o.pairedRepresentation f hf hker

/-- The normalizer of the literal marked q(J(S_E)) fixes the actual marker pointwise. -/
theorem normalizer_fixes_projected
    (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
    (hNJ : normalizer (elementaryAbelianMaxJ (lineT T E) : Set G) ≤ M) :
    let := o.module_normal
    let := o.module_elementary
    ∀ g ∈ normalizer (markedThompson T V E : Set I),
      ∀ w ∈ projected o f hf hker, σ g w = w := by
  let := o.module_normal
  let := o.module_elementary
  dsimp only
  intro g hg w hw
  obtain ⟨x,hx,hxg⟩ := g.property
  have hJC : elementaryAbelianMaxJ (localCentralizer T V E) ≤ localCentralizer T V E :=
    sSup_le fun _ hA => hA.1
  have hxC : x ∈ localCentralizer T V E := hJC hx
  have hmap : (markedThompson T V E).map (I).subtype = (J).map q :=
    map_subgroupOf_eq_of_le (marked_map_le_actor o)
  have hn : g.val ∈ normalizer ((J).map q : Set (H ⧸ Q)) := by
    have hh := (markedThompson T V E).le_normalizer_map (I).subtype
      (mem_map_of_mem (I).subtype hg)
    rwa [hmap] at hh
  have hxM := normalizer_lift_mem_M o hJ hNJ x (hxg.symm ▸ hn)
  rw [← hxg]
  exact (fixes_iff_displacement o f hf hker x hxC).mpr
    (displacement_of_mem_M o x hxC hxM) w hw

/-- All six source-marker obligations, proved from the preceding original local hypotheses. -/
theorem facts
    (hNM : normalizer (V : Set G) ≤ M)
    (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
    (hprod : (lineNormalizer E : Set G) = (lineI E : Set G) * (lineM M E : Set G))
    (hNJ : normalizer (elementaryAbelianMaxJ (lineT T E) : Set G) ≤ M) :
    Facts o f hf hker where
  nonzero := projected_nonzero o f hf hker
  sylow_fixed := sylow_fixes_projected o f hf hker
  orbit_span := projected_orbit_span o hNM hprod f hf hker
  displacement x hx hfix := (fixes_iff_displacement o f hf hker x hx).mp hfix
  normalizer_fixed := normalizer_fixes_projected o f hf hker hJ hNJ
  intersection := fixes_iff_mem_M o f hf hker hNM

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker
