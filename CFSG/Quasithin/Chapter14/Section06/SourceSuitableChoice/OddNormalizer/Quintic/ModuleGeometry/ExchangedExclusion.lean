module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedSource
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.PerfectFactorExclusion

/-!
# Applying the terminal comparison to the exchanged source factors

The already constructed exchanged factor data has genuine C-components
with PSL₂(16) core quotients. Applying the complete perfect-factor comparison
to its second-normalizer geometry now gives a contradiction, without any
extra contained/outer component comparison premise.

Only the original module marking, opposite-support centralization and
conjugated point-centralizer identity remain explicit in this branch.
Their proofs, the residual branch and final p=3 assembly remain with
qt-e-14615-quintic-exclusion. Earlier14.6.12--14 retain final discharge with
qt-e-suitable-odd-normalizer. This conditional source application is not the
completed original14.6.15 theorem.
Source: Aschbacher–Smith 14.6.15, printed pp.1034–1035.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
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

variable (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T))
    (hfirst : residual H1 ≤ b.K1) (hsecond : residual H2 ≤ b.K2)
    (hcent1 : firstSupport a H1 ≤ centralizer (b.K2 : Set G))
    (hcent2 : firstSupport a H2 ≤ centralizer (b.K1 : Set G))
    (hconjugate : closure {x : G |
      x ∈ (residualClosure H Mc).map (MulAut.conj s.critical.endpoint.representative).toMonoidHom ⊓
        centralizer (centralInvolutions T : Set G) ∧ orderOf x = 5} =
      b.K2.map (MulAut.conj s.critical.endpoint.representative).toMonoidHom)

include hfirst hsecond hcent1 hcent2 hconjugate in
/-- The actual exchanged source components cannot satisfy the source module
geometry. The remaining hypotheses are precisely the module obligations
of the existing constructor; the terminal component comparison is proved. -/
theorem exchanged_source_exclusion : False := by
  let d := exchangedNormalizerGeometry s b hfirst hsecond hcent1 hcent2 hconjugate
  have he := exchangedNormalizerGeometry_factors s b hfirst hsecond hcent1 hcent2 hconjugate
  apply source_exchanged_geometry_false s d
  · rw [show d.K1 = b.K1 from he.1]
    exact b.first_component
  · rw [show d.K2 = b.K2 from he.2]
    exact b.second_component
  · rw [show d.K1 = b.K1 from he.1]
    exact b.first_model

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
