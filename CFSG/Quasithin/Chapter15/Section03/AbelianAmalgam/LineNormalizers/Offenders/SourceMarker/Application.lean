module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceMarker
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceAssembly

/-!
# Applying the constructed marker to the source offender assembly

The proved marker geometry instantiates SourceAssembly.temporarySource for
the original paired representation. This discharges the local marker premise;
the genuine earlier classification witnesses and original-I₀ final assembly
remain with the source-theorem owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154 (PDF pp.1170–1171).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker.Application
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer
  BestReduction.SourceAssembly
universe u
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {K : GroupClass.{u}} {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)
  (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
  (hNM : normalizer (V : Set G) ≤ M) (hI : ¬ lineI E ≤ lineM M E)
  (hprod : (lineNormalizer E : Set G) = (lineI E : Set G) * (lineM M E : Set G))
  (hNJ : normalizer (elementaryAbelianMaxJ (lineT T E) : Set G) ≤ M)
  (hG : IsSQTK K (lineNormalizer E))
  (Z : Subgroup G) (hZV : Z ≤ V)
  (hZ : Nat.Coprime 3 (Nat.card (normalizer (Z : Set G))))
  (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))

/-- The actual temporary source, with the marker geometry discharged from the
original local conclusions. Earlier classification witnesses remain with the
original-I₀ assembly owner. -/
noncomputable def temporarySource :
    let := o.module_normal
    let := o.module_elementary
    TemporarySource K Y T V E L (o.pairedRepresentation f hf hker) :=
  SourceAssembly.temporarySource o hJ hNM hI hG Z hZV hZ f hf hker
    (facts o f hf hker hNM hJ hprod hNJ)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker.Application
