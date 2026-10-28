module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.CentralCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Offenders
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Orthogonal
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# The genuine L₄ module alternatives

The Thompson relation constructs offenders for the literal conjugation
action of `L/O₂(L)` on `U_L = [W_L,L]`. Faithfulness, simplicity and the
full commutator identity discharge every B.5.1 input. The universal table
then gives the orthogonal fixed-space quotient, natural plus dual, or
one to three isomorphic natural summands. The actual parabolic and the
nontrivial `[Z,Y₊]` action exclude the orthogonal quotient, including its
central cover. The surviving coordinates retain their own model markings.

The theorem takes the precise earlier source conclusions and the actual
inner-action and plane-parabolic preparation outputs. Elementarity of
the span and its commutator, and innerness on `LR`, are derived here.
Only the genuine universal B.5.1/B.4.2 classification and I.1.6(6)
cohomology witnesses remain as classification inputs. The parent owns
their instantiation, the earlier inputs and the rest of 15.3.24; this
module proves its requested `ModuleAlternatives` step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 and
15.3.24, printed pp.99 and 1129, using B.2.4–14, B.4.2 and I.1.5–6,
printed pp.75–78, 86 and 408.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives
open RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization

universe u
variable {G : Type u} [Group G] [Finite G] (d : LocalData G)
  {I : Subgroup G} (c : ComponentWitness d I)

/-- The module-alternatives step of 15.3.24, from the genuine earlier
conclusions and preparation outputs. `hW`, `hred`, `hLRcore` and `hJ` are
the span, two-reducedness, core bound and Thompson relation of 15.3.16.
The centralizer bounds and nontrivial seed action are the earlier local
facts used on printed p.1129. No FF input, local classification output,
or orthogonal-exclusion premise is assumed. -/
theorem moduleAlternatives (classification : Sieve.UniversalFFClassification.{u,u})
    (cohomology : Sieve.UniversalNaturalCohomology)
    (hI : I ∈ d.Hplus) (earlier : Preparation.Earlier d c)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple I)
    (model : (c.L ⧸ pCore 2 c.L) ≃* Projective 4)
    (inner : Preparation.IsInnerOnComponent d c.L earlier.sylow_normalizes_component)
    (plane : PlaneParabolic d c.L model)
    (hW : d.componentSpan c.L ≤ c.L ⊔ d.R)
    (hred : IsR2Within (d.componentSpan c.L) (c.L ⊔ d.R))
    (hLRcore : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (hJ : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hR : d.R ≤ centralizer (d.V : Set G))
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hact : ⁅d.Z, d.Yplus⁆ ≠ ⊥) : ModuleAlternatives d c.L := by
  let _ := hred.elementary
  let _ : IsElementaryAbelian 2 (d.componentSpan c.L) :=
    IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hW).toMonoidHom
      (subgroupOfEquivOfLe hW).surjective
  let _ := commutator_elementary d c.L
  have hRS : d.R ≤ d.S := OutsideStructure.LocalBranches.r_le_s d I hI earlier.sylow
  have hn := hRS.trans earlier.sylow_normalizes_component
  have hi := Offenders.inner_on_join_of_sylow d c.L hn
    earlier.sylow_normalizes_component hRS inner
  have hFF := Offenders.ffInput d c earlier.core_le_R hR model hSQTK
    earlier.yplus_le hn hi hW hred hLRcore hJ hC
  let alternating : (⊤ : Subgroup (c.L ⧸ pCore 2 c.L)) ≃* alternatingGroup (Fin 8) :=
    Subgroup.topEquiv.trans (model.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)
  rcases Sieve.unmarkedCases classification cohomology hFF alternating with ho | hd | hr
  · exact (Orthogonal.source_exclusion d c earlier model plane hR hact ho).elim
  · obtain ⟨_, ⟨hd⟩⟩ := hd
    exact Or.inr ⟨naturalDualCoordinates d c.L earlier.core_le_R hR hd⟩
  · obtain ⟨r, hr, hb, ⟨h⟩⟩ := hr
    exact Or.inl ⟨r, hr, hb, ⟨repeatedCoordinates d c.L earlier.core_le_R hR h⟩⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives

end
