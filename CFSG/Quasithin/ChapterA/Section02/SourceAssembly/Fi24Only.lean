module
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Induction
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.ONanLocalInversion
/-!
# Simultaneous A/B/C with the O'Nan source branch discharged

The genuine odd-central O'Nan local-rank obstruction closes its original
counterexample branch. The only remaining input is the actual Fi24 involution-
centralizer quotient onto Fi22, shared by the simple and nonsemisimple cases.
Source: Aschbacher--Smith A.2.1--3, A.2.19, printed pp.33--41.
-/
public section
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
/-- The complete simultaneous induction, retaining only the actual Fi24 section. -/
theorem theoremsABC_of_fi24_source
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier) :
    TheoremsABC KnownSimple.IsKnownSimple G := by
  apply theoremsABC_of_fi24_onan_source d24
  intro X Y _ _ _ _ _ p h ih e
  exact Sporadic.SourceAssembly.WithoutPrimeCore.cover_onan_of_local_inversion h ih e
end CFSG.Quasithin.ChapterA.Section02
