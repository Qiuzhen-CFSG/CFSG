module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicSylowImage
public import Theory.SpecificGroups.Janko4.Model.CubicSylowQuotient

/-!
# The marked cubic-product quotient in the original Hall branch

The existing native action uses the containing component's actual simple-section
projection and maps the original T onto a full Sylow S. Sylow self-normalization
sharpens the index-three actor product to an S₃ quotient by its two-core.
Its core has order 2²⁰ and central omega order at most four; the actual quotient
map sends the original Sylow and actor images to groups of orders two and three.

The Hall application retains both covering components, the entire original
involution-centralizer seed, the full fixed-residual equality, the replacement
product and inclusion-induced quotient markings. The same original action
and replacement marking supply the new quotient data.

This does not yet prove that the original T fixes the replacement's selected
involution. That normalization, the M₁₂/M₂₂ pushing-up comparisons, M₂₄ fixed
line, seed generation and separate odd-normalizer assembly are still required
for SourceMathieuHallFaithfulAt.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 4.4.3,
printed p.623, used in 4.4.14, pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4.Section04.OddLocalMathieu

/-- The original native Sylow image with the exact quotient and both marked images. -/
@[expose] def CubicSylowQuotientAt {G : Type*} [Group G]
    (T C A : Subgroup G) (Q : Subgroup C) [Q.Normal]
    (e : SimpleSection Q ≃* Janko4.Model) : Prop :=
  ∃ S : Sylow 2 Janko4.Model,
    (S : Subgroup Janko4.Model) = (T.subgroupOf C).map (cubicNativeAction Q e) ∧
    let B := (A.subgroupOf C).map (cubicNativeAction Q e)
    let M := B ⊔ (S : Subgroup Janko4.Model)
    Nat.card B = 3 ∧
    (B : Set Janko4.Model)*(S : Set Janko4.Model) =
      (S : Set Janko4.Model)*(B : Set Janko4.Model) ∧
    (S : Subgroup Janko4.Model).relIndex M = 3 ∧
    (M.pCoreIn 2).relIndex (S : Subgroup Janko4.Model) = 2 ∧
    Nat.card (center S) = 2 ∧
    Nat.card (pCore 2 M) = 2^20 ∧
    Nat.card (omega₁ (center (pCore 2 M)) (p := 2)) ≤ 4 ∧
    ∃ f : (M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 3),
      let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
      Nat.card (((S : Subgroup Janko4.Model).subgroupOf M).map q) = 2 ∧
      Nat.card ((B.subgroupOf M).map q) = 3

/-- The checked native normalizer calculation discharges all added quotient facts. -/
theorem cubicSylowQuotientAt_of_image {G : Type*} [Group G]
    {T C A : Subgroup G} {Q : Subgroup C} [Q.Normal]
    {e : SimpleSection Q ≃* Janko4.Model} (h : CubicSylowImageAt T C A Q e) :
    CubicSylowQuotientAt T C A Q e := by
  obtain ⟨S,hS,hB,hperm,hindex,hcore,hcenter⟩ := h
  obtain ⟨hi,hcard,hbound,f,hfS,hfB⟩ := Janko4.cubic_sylow_quotient S
    ((A.subgroupOf C).map (cubicNativeAction Q e)) hB hindex
  exact ⟨S,hS,hB,hperm,hindex,hi,hcenter,hcard,hbound,f,hfS,hfB⟩

/-- Forgetting the sharper facts recovers the original native-image interface. -/
theorem CubicSylowQuotientAt.to_image {G : Type*} [Group G]
    {T C A : Subgroup G} {Q : Subgroup C} [Q.Normal]
    {e : SimpleSection Q ≃* Janko4.Model} (h : CubicSylowQuotientAt T C A Q e) :
    CubicSylowImageAt T C A Q e := by
  obtain ⟨S,hS,hB,hperm,hindex,hcore,hcenter,_⟩ := h
  exact ⟨S,hS,hB,hperm,hindex,hcore.le,hcenter⟩
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Sporadic.Mathieu
/-- The full original cubic witnesses, including the marked S₃ quotient of the
original actor--Sylow product under the replacement’s component marking. -/
@[expose] def MathieuJankoCubicQuotientCase {G : Type*} [Group G]
    (T L V A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    ∃ a : JankoNormalizerAction K,
      a.ResidualSeedFamily ∧ center K = ⊥ ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        Nonempty ((centralizer ({z} : Set K) ⧸
          pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
            Janko4.InvolutionCentralizers.First.centralizer) ∧
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
                  ((pCore 2 P).map (OddLocalMathieu.seedInclusion inf_le_left hPQ) ≤
                      pCore 2 Q) ∧
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
                        (t : Janko4.Model),
                        CubicSylowQuotientAt T
                          (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G))
                          A Q e ∧ orderOf t = 2 ∧
                        (∀ c : centralizer ({((z : normalizer (A : Set G)) : G)} : Set G),
                          MulAut.congr e (OddLocalMathieu.simpleAction Q c) t = t →
                            (c : G) ∈ normalizer (I : Set G)) ∧
                        (R.subgroupOf Q).map (e.toMonoidHom.comp (OddLocalMathieu.projection Q)) =
                          (solvableResidual (centralizer ({t} : Set Janko4.Model))).map
                            (centralizer ({t} : Set Janko4.Model)).subtype

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 OddLocalMathieu
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V A : Subgroup G}

/-- Strengthen the original product without changing any component, seed or marking. -/
theorem mathieu_janko_cubic_quotient
    (hc : MathieuJankoCubicSylowCase (T : Subgroup G) L V A) :
    MathieuJankoCubicQuotientCase (T : Subgroup G) L V A := by
  obtain ⟨K,hK,hn,hout,hV,hF,a,hseed,hZ,z,hzV,hz,hfirst,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hdata,hcore,
    I,hPI,hfull,heI,hIQ,hAI,hperf,hqI,eI,R,hIR,hRQ,e,t,hSylow,ht,hnorm,himage⟩ := hc
  let := hnQ
  exact ⟨K,hK,hn,hout,hV,hF,a,hseed,hZ,z,hzV,hz,hfirst,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hdata,hcore,
    I,hPI,hfull,heI,hIQ,hAI,hperf,hqI,eI,R,hIR,hRQ,e,t,
    cubicSylowQuotientAt_of_image hSylow,ht,hnorm,himage⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction supplies the exact S₃ quotient of its
original cubic product, preserving the full seed and replacement marking. -/
theorem sourceOrbit_mathieu_hall_cubic_quotient
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
            (p = 3 ∧ MathieuJankoCubicQuotientCase (T : Subgroup G) L V A)))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_cubic_sylow G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hcases⟩ := hA
  refine ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,?_⟩
  apply Or.imp id _ hcases
  intro hc
  exact ⟨hc.1,hc.2.1,hc.2.2.imp id (fun ht =>
    ⟨ht.1,mathieu_janko_cubic_quotient ht.2⟩)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
