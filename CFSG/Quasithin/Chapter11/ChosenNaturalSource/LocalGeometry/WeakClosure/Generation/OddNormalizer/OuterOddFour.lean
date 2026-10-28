module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterSymplecticSix
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.SpecialFourFrattini

/-!
# Excluding the odd four-dimensional outer component rows

The determinant-one degree-four bound gives Sylow Frattini quotient order
at most 32 in each actual SL₄, SU₄ and Sp₄ cover. Surjective quotient
transport preserves that bound in the source's projective models.
The PSL₃(4) section obstruction excludes the original outer action on
all three families, including every allowed Fermat and Mersenne parameter.
Together with the binary Sp₆ exclusion this leaves only odd-prime G₂.

The Source endpoint applies the result to the same component of N_G(A)
and the literal Hall kernel. The original V, full SL₃(4) quotient and
central cubic are retained. Odd G₂ and moved J₄ remain with this task;
ordinary C.2.8 remains with qt-d-1222-natural-point-fixed-summand, and
final 11.2.1 assembly with qt-d-1222-natural-weak-closure-source.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, using I.3.1.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {F : Type*} [Field F] [Finite F]

private theorem psl_four_frattini_le_thirtytwo (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 PSL(4,F)) : Nat.card (P ⧸ frattini P) ≤ 32 := by
  apply Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
    (QuotientGroup.mk' (center SL(4,F))) (QuotientGroup.mk'_surjective _) ?_ P
  intro Q
  exact SpecialFourFrattini.special_degree_four_frattini_le_thirtytwo Q.isPGroup'
    (Matrix.SpecialLinearGroup.toGL.comp (Q : Subgroup SL(4,F)).subtype)
    (Matrix.SpecialLinearGroup.toGL_injective.comp Subtype.val_injective) h2
    (fun q => Matrix.SpecialLinearGroup.coeToGL_det q.val)

private theorem psu_four_frattini_le_thirtytwo
    (J : BenderSuzuki.MatrixGroups.HermitianForm 4 F) (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) ≤ 32 := by
  apply Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
    (Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup)
    (Matrix.ProjGenLinGroup.mk.subgroupMap_surjective J.specialSubgroup) ?_ P
  intro Q
  exact SpecialFourFrattini.special_degree_four_frattini_le_thirtytwo Q.isPGroup'
    (J.specialSubgroup.subtype.comp (Q : Subgroup J.specialSubgroup).subtype)
    (Subtype.val_injective.comp Subtype.val_injective) h2 (fun q => q.val.property.2)

open Theory.SpecificGroups.SymplecticFour
private def symplecticToGL : Sp F →* GL (Fin 2 ⊕ Fin 2) F where
  toFun g := Matrix.GeneralLinearGroup.mk'' g.val (SymplecticGroup.symplectic_det g.property)
  map_one' := by apply Units.ext; rfl
  map_mul' _ _ := by apply Units.ext; rfl

private theorem psp_four_frattini_le_thirtytwo (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 (Sp F ⧸ center (Sp F))) : Nat.card (P ⧸ frattini P) ≤ 32 := by
  let e : (Fin 2 ⊕ Fin 2) ≃ Fin 4 := finSumFinEquiv
  let r : GL (Fin 2 ⊕ Fin 2) F ≃* GL (Fin 4) F :=
    Units.mapEquiv (Matrix.reindexRingEquiv F e).toMulEquiv
  let rho := r.toMonoidHom.comp symplecticToGL
  have hrho : Function.Injective rho := r.injective.comp (fun _ _ h =>
    Subtype.ext (congrArg Units.val h))
  have hdet (g : Sp F) : Matrix.GeneralLinearGroup.det (rho g) = 1 := by
    apply Units.ext
    change Matrix.det (Matrix.reindex e e g.val) = 1
    rw [Matrix.det_reindex_self]
    exact SymplecticGroup.det_eq_one g.property
  apply Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
    (QuotientGroup.mk' (center (Sp F))) (QuotientGroup.mk'_surjective _) ?_ P
  intro Q
  exact SpecialFourFrattini.special_degree_four_frattini_le_thirtytwo Q.isPGroup'
    (rho.comp (Q : Subgroup (Sp F)).subtype)
    (hrho.comp Subtype.val_injective) h2 (fun q => hdet q.val)

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The determinant-one degree-four bound excludes each actual odd
four-dimensional component quotient from the original outer action. -/
theorem moved_outer_not_odd_four {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hB : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f) {q : ℕ} (hq : Odd q) :
    ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 q ∧
      ¬ ClassicalGroup.IsPSU (K ⧸ center K) 4 q ∧
      ¬ ClassicalGroup.IsPSp (K ⧸ center K) 2 q := by
  let P : Sylow 2 (K ⧸ center K) := default
  have exclude := moved_outer_not_of_frattini_le_thirtytwo D S K hK ho hB P
  refine ⟨fun hm => ?_,fun hm => ?_,fun hm => ?_⟩
  · apply exclude
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup (K ⧸ center K)))]
    exact psl_four_frattini_le_thirtytwo
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) hq
        (by simpa using hF)) (P.mapSurjective e.surjective)
  · apply exclude
    obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup (K ⧸ center K)))]
    exact psu_four_frattini_le_thirtytwo J
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card hq hF)
      (P.mapSurjective e.surjective)
  · apply exclude
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup (K ⧸ center K)))]
    exact psp_four_frattini_le_thirtytwo
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) hq
        (by simpa using hF)) (P.mapSurjective e.surjective)

/-- Only the actual odd-prime G₂ row survives the original outer section. -/
theorem moved_outer_g2_model {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassificationModels.IsG2At (K ⧸ center K) p := by
  rcases moved_outer_odd_models D S K hK hm ho with hp | hg | hl | hu
  · obtain ⟨p,_,hp,he⟩ := hp
    exact ((moved_outer_not_odd_four D S K hK hm ho hp).2.2 he).elim
  · exact hg
  · obtain ⟨r,_,⟨k,hk⟩,he⟩ := hl
    have hr : Odd r := by
      rw [hk]
      exact (even_two.pow_of_ne_zero (by positivity)).add_one
    exact ((moved_outer_not_odd_four D S K hK hm ho hr).1 he).elim
  · obtain ⟨s,hs,⟨b,hb⟩,he⟩ := hu
    have hb0 : b ≠ 0 := by intro hh; subst b; norm_num at hb; have := hs.two_le; omega
    have hseven : Even (s+1) := hb.symm ▸ even_two.pow_of_ne_zero hb0
    have hso : Odd s := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hseven)
    exact ((moved_outer_not_odd_four D S K hK hm ho hso).2.1 he).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
