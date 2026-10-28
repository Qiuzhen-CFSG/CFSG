module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.KernelModule
public import CFSG.Quasithin.Chapter10.SourceA5OriginalSeparatedPassage
/-!
# The original separated Hall kernel fixes the full module

The completed original full/local passage supplies bounded coordinates of
the faithful full actor. Their centralizer calculation places the whole
orbit section kernel in C_G(V). This is the original Hall-placement input,
without a coordinate witness or an assumed commutant theorem.
Source: Aschbacher–Smith 10.2.3, p.745, using D.3.21 and 10.1.3.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Earlier minimality, the full cubic bound and separated support suffice
for centralization of the actual full module by the whole section kernel. -/
theorem source_a5_hall_sectionKernel_centralizes_of_separated_seed
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G) :=
  source_a5_hall_sectionKernel_centralizes_of_bounded_coordinates D e hn ht htn
    (source_a5_original_bounded_separated_coordinates D e hn ht htn hD hbound hsep)
end CFSG.Quasithin.Chapter10
