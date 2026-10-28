module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Factorization
public import Theory.Frattini.ConjugateCentralFactors

/-!
# The rank-one Frattini invariance

The source factorizations give the central elementary supplements required
by the general Frattini theorem. This is C.5.6(4), printed p.157, on the
original D=C_S(K), with no assumption that its Frattini subgroup vanishes.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

theorem Setup.frattini_invariant (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    ((frattini (D R L)).map (D R L).subtype).map (MulAut.conj x⁻¹).toMonoidHom =
      (frattini (D R L)).map (D R L).subtype := by
  have hf := h.factorization hx hnc
  exact frattini_conjugate_central_factors (S R) (U L) (Q R L) (D R L) (MulAut.conj x⁻¹)
    (h.stable hx) h.core hf.core hf.centralizes hf.span h.elementary
    (isPGroup_pCoreIn 2 (L ⊔ S R)) (S_normalizes_Q R L)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
