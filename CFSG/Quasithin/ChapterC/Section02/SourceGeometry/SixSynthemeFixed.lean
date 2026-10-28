module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SixTransitiveFixed
public import Theory.SpecificGroups.SymmetricSix.Parabolics.SynthemeTransitive

/-!
# Fixed vectors for a syntheme-marked natural A₆ section

A two-perfect nontrivial image normalized by a conjugate syntheme stabilizer
acts transitively on the six letters. The natural-section cocycle calculation
then makes each vector it fixes centralize the original component through
the literal star action and quotient maps. No splitting of the ambient binary
module extension is required.

Source application: Aschbacher–Smith, C.2.7 and 15.3.21, combined manuscript
of 1 March 2004, pp.145–147 and1127.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G]

/-- An actual star vector fixed by the syntheme residual centralizes L. -/
theorem star_alternatingSix_syntheme_fixed_centralizes
    (L R : Subgroup G) :
    let C := starImage L R L
    let J := offenderSubgroup (starRepresentation L R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation L R).comp J.subtype) (C.subgroupOf J))
      (e : ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (alternatingNatural 6))
      (g : Equiv.Perm (Fin 6)) (A : Subgroup (alternatingGroup (Fin 6)))
      (_hAS : A ≤ Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer.map
        (MulAut.conjNormal g).toMonoidHom)
      (_hAN : Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer.map
        (MulAut.conjNormal g).toMonoidHom ≤
        normalizer (A : Set (alternatingGroup (Fin 6))))
      (_hA : IsPPerfect 2 A) (_hne : A ≠ ⊥)
      (w : Additive (starV L R))
      (_hw : ∀ a : A, ((starRepresentation L R).comp J.subtype)
        (e.groupEquiv.symm a) w = w),
      ((w.toMul : (L ⊔ R : Subgroup G)) : G) ∈ centralizer (L : Set G) := by
  intro C J hCJ s e g A hAS hAN hA hne w hw
  exact star_alternatingSix_fixed_centralizes L R hCJ s e A hA
    (Theory.SpecificGroups.SymmetricSix.conjugate_syntheme_normal_twoPerfect_transitive
      g A hAS hAN hA hne) w hw

end CFSG.Quasithin.ChapterC.C27Source
