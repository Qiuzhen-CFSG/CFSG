module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicReplacement
public import Theory.GroupTheory.CComponent.RadicalQuotientCover

/-!
# The full-cover product for the exceptional cubic replacement

The constructed replacement I contains the original involution-centralizer
residual K_Z. Both have radical quotient M₂₂, and I/O₂(I) is quasisimple.
The general radical-quotient comparison therefore proves I = K_Z O₂(I).
The resulting isomorphism K_Z/O₂(K_Z) ≃ I/O₂(I) is induced by the original
seed inclusion, retaining the complete central cover.

The literal Hall application records that product with the original full
J₄ component, its involution centralizer, and the existing quotient maps.
It also retains the replacement's exact native residual image and the odd
actor's trivial action modulo O₂(I). T-normalization, the M₁₂/M₂₂ pushing-up
exclusions, and the final fixed-line and seed-generation comparisons remain
open. This module does not assert SourceMathieuHallFaithfulAt.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 4.4.3,
printed p.623, applied in 4.4.14, printed pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Sporadic.Mathieu

/-- The original seed covers the replacement's full two-core quotient;
the isomorphism is induced by the original inclusion on every element. -/
theorem cubic_replacement_seed_cover
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) (P : Subgroup E) (I : Subgroup G)
    (hPI : P.map E.subtype ≤ I) [IsQuasisimple (I ⧸ pCore 2 I)]
    (eP : (P ⧸ solvableRadical P) ≃* M22)
    (eI : (I ⧸ solvableRadical I) ≃* M22) :
    (I : Set G) = (P.map E.subtype : Set G) * (I.pCoreIn 2 : Set G) ∧
      ∃ e : (P ⧸ pCore 2 P) ≃* (I ⧸ pCore 2 I),
        ∀ p : P, e (QuotientGroup.mk' (pCore 2 P) p) =
          QuotientGroup.mk' (pCore 2 I) ⟨(p : E),hPI (mem_map_of_mem E.subtype p.property)⟩ := by
  let F := P.map E.subtype
  let a : P ≃* F := P.equivMapOfInjective E.subtype E.subtype_injective
  let ar := QuotientGroup.congr (solvableRadical P) (solvableRadical F) a
    (map_solvableRadical_equiv a)
  have hc : Nat.card (I ⧸ solvableRadical I) ≤ Nat.card (F ⧸ solvableRadical F) :=
    (Nat.card_congr (eI.trans (ar.symm.trans eP).symm).toEquiv).le
  have hcover := subgroup_cover_twoCore_of_radical_quotient_card F I hPI hc
  obtain ⟨e,he⟩ := Subgroup.exists_pCoreQuotientEquiv_of_cover (p := 2) hPI hcover.subset
  let d := QuotientGroup.congr (pCore 2 P) (pCore 2 F) a (pCore_map_iso 2 a)
  refine ⟨hcover,d.trans e,?_⟩
  intro p
  change e (QuotientGroup.mk' (pCore 2 F) (a p)) = _
  rw [he]
  rfl

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Sporadic.Mathieu
/-- The concrete replacement covers exactly the original seed modulo its two-core,
with the inclusion-induced quotient marking. Original T-normalization is still open. -/
@[expose] def MathieuJankoCubicCoveredReplacementCase {G : Type*} [Group G]
    (T L V A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    ∃ a : JankoNormalizerAction K,
      a.ResidualSeedFamily ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        T ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
        ∃ P : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G) : Subgroup G),
          P.IsCComponent ∧ P.Normal ∧ Nonempty ((P ⧸ solvableRadical P) ≃* M22) ∧
          P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G)).subtype =
              ((solvableResidual (centralizer ({z} : Set K))).map
                (centralizer ({z} : Set K)).subtype).map
                  ((normalizer (A : Set G)).subtype.comp K.subtype) ∧
          ∃ Q : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
            Q.IsCComponent ∧ ∃ hPQ : P.map (inclusion inf_le_left) ≤ Q,
              ∃ hn : Q.Normal, letI := hn
              IsQuasisimple (Q ⧸ pCore 2 Q) ∧
              Nonempty (OddLocalMathieu.SimpleSection Q ≃* Janko4.Model) ∧
              ∃ hAz : A ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G),
                ∃ x : A, orderOf (OddLocalMathieu.simpleAction Q ⟨x,hAz x.property⟩) = 3 ∧
                  Nat.card ((OddLocalMathieu.simpleAction Q).comp (inclusion hAz)).range = 3 ∧
                  (let f := (OddLocalMathieu.projection Q).comp
                      (OddLocalMathieu.seedInclusion inf_le_left hPQ)
                   let b := (OddLocalMathieu.simpleAction Q).comp (inclusion hAz)
                   f.range = (solvableResidual (b x).fixedSubgroup).map
                     (b x).fixedSubgroup.subtype ∧
                   ∃ y : center f.range, orderOf y = 3 ∧
                     MulAut.conj ((y : f.range) : OddLocalMathieu.SimpleSection Q) = b x ∧
                     b.range = (zpowers ((y : f.range) : OddLocalMathieu.SimpleSection Q)).map
                       MulAut.conj) ∧
                  ∃ I : Subgroup G,
                    ∃ hPI : P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
                      centralizer (A : Set G)).subtype ≤ I,
                    ((I : Set G) =
                      (((solvableResidual (centralizer ({z} : Set K))).map
                        (centralizer ({z} : Set K)).subtype).map
                          ((normalizer (A : Set G)).subtype.comp K.subtype) : Set G) *
                        (I.pCoreIn 2 : Set G)) ∧
                    (∃ e : (P ⧸ pCore 2 P) ≃* (I ⧸ pCore 2 I),
                      ∀ p : P, e (QuotientGroup.mk' (pCore 2 P) p) =
                        QuotientGroup.mk' (pCore 2 I)
                          ⟨(p.val : G),hPI (mem_map_of_mem _ p.property)⟩) ∧
                    I ≤ Q.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype ∧
                    A ≤ sectionCentralizer I ∧ Group.IsPerfect I ∧
                    IsQuasisimple (I ⧸ pCore 2 I) ∧
                    Nonempty ((I ⧸ solvableRadical I) ≃* M22) ∧
                    ∃ R : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
                      I = R.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype ∧
                      R ≤ Q ∧ ∃ (e : OddLocalMathieu.SimpleSection Q ≃* Janko4.Model)
                        (t : Janko4.Model), orderOf t = 2 ∧
                        (∀ c : centralizer ({((z : normalizer (A : Set G)) : G)} : Set G),
                          MulAut.congr e (OddLocalMathieu.simpleAction Q c) t = t →
                            (c : G) ∈ normalizer (I : Set G)) ∧
                        (R.subgroupOf Q).map (e.toMonoidHom.comp (OddLocalMathieu.projection Q)) =
                          (solvableResidual (centralizer ({t} : Set Janko4.Model))).map
                            (centralizer ({t} : Set Janko4.Model)).subtype

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T L V A : Subgroup G}

/-- The constructed exceptional replacement has exactly the original seed's
two-core quotient, with its full covering center and original map retained. -/
theorem mathieu_janko_cubic_covered_replacement
    (hc : MathieuJankoCubicReplacementCase T L V A) :
    MathieuJankoCubicCoveredReplacementCase T L V A := by
  obtain ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hdata,
    I,hPI,hIQ,hAI,hperf,hqI,eI,htail⟩ := hc
  let := hqI
  have hcover := cubic_replacement_seed_cover _ P I hPI eP.some eI.some
  have hfull := hcover.1
  rw [hPm] at hfull
  exact ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hdata,
    I,hPI,hfull,hcover.2,hIQ,hAI,hperf,hqI,eI,htail⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction supplies the source replacement product and
its original inclusion-induced quotient isomorphism. Every prior component,
Hall map and fixed-residual equality is retained. T-normalization remains open. -/
theorem sourceOrbit_mathieu_hall_cubic_covered_replacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (((Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
          Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
          MathieuPushingUpFactoredCase T L V A ∧ MathieuPushingUpFactorGap T L V A) ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent) ∧
          (MathieuJankoComparedResidualCase (T : Subgroup G) L V A ∨
            (p = 3 ∧ MathieuJankoCubicCoveredReplacementCase (T : Subgroup G) L V A)))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_cubic_replacement G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  revert hA
  iterate 11 apply And.imp_right
  apply Or.imp id
  intro hc
  exact ⟨hc.1,hc.2.1,hc.2.2.imp id (fun ht =>
    ⟨ht.1,mathieu_janko_cubic_covered_replacement ht.2⟩)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
