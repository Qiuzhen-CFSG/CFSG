module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductSeed
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.CComponent.ThreeCore
public import Theory.Alternating.PrimeRank
public import Theory.Alternating.Aut

/-!
# The normalizer residual after removal of the A₇ central cover

The actual L is a normal C-component in N_G(L). Its two-core quotient A₇
is centerless, has three-rank two, and has a two-group of outer
automorphisms. The original local rank bound and A.3.18 therefore identify
L with O^{3′}(N_G(L)). The argument takes the two-core quotient explicitly;
it does not replace the original central quotient by that quotient.

Source: Aschbacher--Smith, 12.2.8 and 12.3.13, printed pp.797 and 811.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02

private theorem seven_outer_two : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 7))) := by
  let A := alternatingGroup (Fin 7)
  have hcard : Nat.card (Equiv.Perm (Fin 7) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable (S : Setup T L V)

include S in
/-- The second conclusion of 12.3.13, conditional on the first one.
The normality and rank hypotheses are derived in the actual normalizer. -/
theorem Setup.normalizer_residual_of_twoCore_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L := by
  let M := normalizer (L : Set G)
  let X := L.subgroupOf M
  let : X.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : IsQuasisimple (L ⧸ pCore 2 L) := S.hypothesis.quasisimple
  let eX : (X ⧸ pCore 2 X) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe L.le_normalizer) (pCore_map_iso 2 _)
  let : IsQuasisimple (X ⧸ pCore 2 X) := IsQuasisimple.of_mulEquiv eX.symm
  let eA := eX.trans e
  have hX : X.IsCComponent :=
    S.hypothesis.toHypothesis1221.sylow_normalized_component
      S.chosen.sylow_normalizes_component
      (fun H _ _ => ChapterA.Section02.theoremA_knownSimple (G := H))
      (fun H _ _ => ChapterA.Section02.theoremC_knownSimple (G := H))
  have hrM : primeRank 3 M ≤ 2 :=
    (S.hypothesis.toHypothesis1221.sylow_normalized_sqtk
      S.chosen.sylow_normalizes_component
      (fun H _ _ => ChapterA.Section02.theoremA_knownSimple (G := H))
      (fun H _ _ => ChapterA.Section02.theoremC_knownSimple (G := H))).stronglyQuasithin
        3 Nat.prime_three (by decide)
  have hrX : 2 ≤ primeRank 3 (X ⧸ pCore 2 X) := by
    rw [primeRank_congr 3 eA,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 3 Nat.prime_three (by decide)]
  have hz : center (X ⧸ pCore 2 X) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he : eA x ∈ center (alternatingGroup (Fin 7)) := (centerCongr eA ⟨x, hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact eA.map_eq_one_iff.mp he
  have ho : IsPGroup 2 (MulAut.Outer (X ⧸ pCore 2 X)) :=
    seven_outer_two.of_injective (MulAut.outerCongr eA).toMonoidHom
      (MulAut.outerCongr eA).injective
  have he := hX.eq_primeToResidual_three_of_outer_twoGroup hz hrX hrM ho
  have hm := congrArg (map M.subtype) he.symm
  exact hm.trans (map_subgroupOf_eq_of_le L.le_normalizer)

include S in
/-- The existing cover reduction feeds the actual normalizer residual. -/
theorem Setup.normalizer_residual_of_abelian_threeSylow
    (R : Sylow 3 (L ⧸ pCore 2 L)) (hR : IsMulCommutative R) :
    (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L :=
  S.normalizer_residual_of_twoCore_quotient
    (quotientEquivOfAbelianThreeSylow S R hR)

namespace TerminalPoint
variable {S} {D : S.LocalAnalysis} (P : TerminalPoint S D)

/-- The ambient L₁ identity now needs only the abelian cubic Sylow input,
with the source omega-center centralizer bound supplied by LocalAnalysis. -/
theorem L1_eq_ambient_residual_of_abelian_threeSylow
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (R : Sylow 3 (L ⧸ pCore 2 L)) (hR : IsMulCommutative R) :
    P.L1 = (primeToResidual 3 (centralizer (P.Z : Set G))).map
      (centralizer (P.Z : Set G)).subtype :=
  P.L1_eq_ambient_residual structural (S.normalizer_residual_of_abelian_threeSylow R hR)

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
