module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualSigned
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedFactors
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.LinearExclusion

/-!
# Excluding the original residual branch of 14.6.15

The signed Sylow marking constructs the actual second-normalizer geometry
when K_z = O²(H). The complete component comparisons now contradict that
geometry, so only the exchanged PSL₂(16) closure alternative remains.
The last theorem constructs its actual factor data for the remaining
module-geometric argument.

The exchanged module geometry, original index obligation and final p=3
assembly remain with qt-e-14615-quintic-exclusion. These statements retain
the original Context, including its ExchangedFactorSetup.index premise.
Earlier 14.6.12--14 inputs retain their discharge with
qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith 14.6.15, printed pp.1034--1035.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

include s in
/-- The actual residual closure cannot equal the original residual at p=5. -/
theorem source_residual_exclusion (hc : residualClosure H Mc = residual H) : False :=
  source_normalizer_geometry_false s (sourceResidualNormalizerGeometry s hc)

include s in
/-- The literal fourth alternative is the only surviving source closure. -/
theorem source_exchanged_closure_model :
    ExchangedComponentClosure (T : Subgroup G) Mc (residualClosure H Mc) ∧
      Nonempty ((Mc ⧸ pCore 2 Mc) ≃* Theory.PSL2.SixteenWreathComponents.W) := by
  rcases s.alternatives with h | h | h | h
  · exact (source_residual_exclusion s h.1).elim
  · norm_num at h
  · norm_num at h
  · exact h.2

include s in
/-- Construct the genuine exchanged factors after excluding K_z=K. -/
theorem source_exchanged_factor_data :
    Nonempty (ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T)) :=
  exists_source_exchanged_factor_data s (source_residual_exclusion s)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
