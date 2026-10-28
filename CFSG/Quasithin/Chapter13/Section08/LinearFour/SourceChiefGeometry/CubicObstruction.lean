module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.CubicAccounting
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExclusion
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.Accounting
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Transport

/-!
# Applying the cubic chief counts to the linear-four obstruction

Transport a chief series on L₀ inside H through the literal subgroup-of
isomorphism. Its noncentral count and both intersection endpoints are
preserved. Three noncentral factors then exclude a unique K-factor of
order sixteen; component movement follows from the same count. The
cubic section calculations supply the three-factor bound, so the final
application discharges both 13.8.31(3) inputs of the existing faithful
H/O₂(H) chief-section contradiction.

The natural, exterior, dual and radical markings, their common cubic,
the normalizer geometry, the nine-factor lower bound and the critical
intersection inputs remain explicit source obligations of
qt-d-138-linear-four-source. The genuine earlier setup is supplied by
qt-d-138-six-g2-source; qt-d-1381-source owns final assembly. No assertion
of completion of 13.8.28 is made by this conditional application.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.31(3) and the terminal proof of 13.8.28, printed pp.965–966.
-/

public section
open Subgroup Representation NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

/-- Transport the lower bound to the literal restriction of an H-chief series,
using the subgroup-of equivalence and its original conjugation action. -/
theorem source_ambient_no_unique_four_of_three
    (H K D VH HC : Subgroup G) (hKH : K ≤ H) (hDK : D ≤ K)
    (hthree : ∀ t : ChiefSeries D, t.head.val = VH.subgroupOf D →
      t.last.val = HC.subgroupOf D → 3 ≤ t.noncentralTwoCount)
    (s : ChiefSeries H) (hs0 : s.head.val.map H.subtype = VH)
    (hs1 : s.last.val.map H.subtype = HC)
    (hone : s.restrictedNoncentralCount (K.subgroupOf H) = 1)
    (i : Fin s.length)
    (hi : ¬ ∀ k : K.subgroupOf H, ∀ x,
      sectionAction (s i.castSucc) (s i.succ) k x = x) :
    Nat.card (Section (s i.castSucc) (s i.succ)) ≠ 16 := by
  let D' := D.subgroupOf H
  let e : D' ≃* D := subgroupOfEquivOfLe (hDK.trans hKH)
  apply source_no_unique_four_of_restricted_three H (K.subgroupOf H) D'
    (subgroupOf_mono H hDK) s.head s.last ?_ s rfl rfl hone i hi
  intro t ht0 ht1
  have endpoints (N : NormalNode H) :
      (actorNormalEquiv e (restrictNormalNode D' N)).val =
        (N.val.map H.subtype).subgroupOf D := by
    ext x
    constructor
    · rintro ⟨y,hy,he⟩
      change (x : G) ∈ N.val.map H.subtype
      have hx : (e y : G) = x := congrArg Subtype.val he
      exact hx ▸ mem_map_of_mem H.subtype hy
    · intro hx
      change (x : G) ∈ N.val.map H.subtype at hx
      obtain ⟨y,hy,he⟩ := hx
      have hyD : (y : G) ∈ D := by
        change (y : G) = (x : G) at he
        rw [he]
        exact x.property
      refine ⟨⟨y,hyD⟩,hy,?_⟩
      exact Subtype.ext he
  have h0 : (t.mapActor e).head.val = VH.subgroupOf D := by
    rw [ChiefSeries.mapActor_head,ht0,endpoints,hs0]
  have h1 : (t.mapActor e).last.val = HC.subgroupOf D := by
    rw [ChiefSeries.mapActor_last,ht1,endpoints,hs1]
  simpa using hthree (t.mapActor e) h0 h1

open BinaryParabolicExteriorSquare.PlaneSpan
open Atlas.Order20160A8.Bivectors (exteriorMap)

/-- The literal cubic section calculations supply both clauses of the
13.8.31(3) obstruction consumed by the terminal H-chief-series argument. -/
theorem source_chief_obstruction_of_cubic_sections
    {K : Type*} [Group K] [Finite K]
    (H D UH V1 VH HC QH A : Subgroup G) (hDH : D ≤ H) (hAD : A ≤ D)
    (hA : Nat.card A = 3) (hQH : IsPGroup 2 QH) (hVC : VH ≤ HC)
    (hQHD : QH ≤ normalizer (D : Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (ddual : BinaryConjugationSection H QH HC ρ.dual)
    (ξ : Representation (ZMod 2) H Six)
    (dexterior : BinaryConjugationSection H VH UH ξ)
    (a : A) (ha : ∀ b, b ∈ zpowers a)
    (hnatural : ∀ v, ρ (inclusion (hAD.trans hDH) a) v = Matrix.mulVec planeCubic v)
    (hexterior : ∀ v, ξ (inclusion (hAD.trans hDH) a) v = exteriorMap planeCubic v)
    (f : D →* K) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (X : Subgroup K) [X.Normal] (hX : Nat.card X = 3)
    (hq : IsPGroup 2 (K ⧸ X)) (hAX : (A.subgroupOf D).map f = X)
    (Z U V C Q R : NormalNode D)
    (hZdef : Z.val = V1.subgroupOf D) (hUdef : U.val = UH.subgroupOf D)
    (hVdef : V.val = VH.subgroupOf D) (hCdef : C.val = HC.subgroupOf D)
    (hQdef : Q.val = QH.subgroupOf D)
    (hZ : IsCentral ⊥ Z) (hterminal : HasNoTwoChiefFactors (D ⧸ R.val))
    (Rg : Subgroup G) (hRdef : R.val = Rg.subgroupOf D) (hRg : IsPGroup 2 Rg)
    (τ : Representation (ZMod 2) D (Fin 4 → ZMod 2))
    (dradical : BinaryConjugationSection D Rg (QH ⊓ D) τ)
    (hradical : ∀ v, τ (inclusion hAD a) v = Matrix.mulVec pairedCubic v)
    (hnine : ∀ t : ChiefSeries D, t.head = ⊥ → t.last = ⊤ →
      9 ≤ t.noncentralTwoCount)
    (Kc : Subgroup G) (hKcH : Kc ≤ H) (hDK : D ≤ Kc) :
    (¬ ⁅HC,Kc⁆ ≤ VH) ∧
    (∀ s : ChiefSeries H, s.head.val.map H.subtype = VH →
      s.last.val.map H.subtype = HC →
      s.restrictedNoncentralCount (Kc.subgroupOf H) = 1 →
      ∀ i : Fin s.length, (¬ ∀ k : Kc.subgroupOf H, ∀ x,
        sectionAction (s i.castSucc) (s i.succ) k x = x) →
        Nat.card (Section (s i.castSucc) (s i.succ)) ≠ 16) := by
  have hthree (s : ChiefSeries D) (hs0 : s.head = V) (hs1 : s.last = C) :
      3 ≤ s.noncentralTwoCount :=
    source_three_factors_of_cubic_sections H D UH V1 VH HC QH A hDH hAD hA
      hQH hVC hQHD ρ d ddual ξ dexterior a ha hnatural hexterior f hf hp X hX hq hAX
      Z U V C Q R hZdef hUdef hVdef hCdef hQdef hZ hterminal
      Rg hRdef hRg τ dradical hradical hnine s hs0 hs1
  refine ⟨source_component_moves_of_three_factors D Kc VH HC hDK V C
    hVdef hCdef hVC hthree, ?_⟩
  intro s hs0 hs1 hone i hi
  apply source_ambient_no_unique_four_of_three H Kc D VH HC hKcH hDK ?_
    s hs0 hs1 hone i hi
  intro t ht0 ht1
  exact hthree t (Subtype.ext (ht0.trans hVdef.symm))
    (Subtype.ext (ht1.trans hCdef.symm))

/-- The constructed cubic chief obstruction feeds the actual H/O₂(H)
faithful-section argument, excluding the linear-four branch under the
remaining tensor lower bound and critical intersection geometry. -/
theorem source_linear_four_exclusion_of_cubic_sections
    {K : Type*} [Group K] [Finite K]
    (H D UH V1 VH HC QH A : Subgroup G) (hDH : D ≤ H) (hAD : A ≤ D)
    (hA : Nat.card A = 3) (hQH : IsPGroup 2 QH) (hVC : VH ≤ HC)
    (hQHD : QH ≤ normalizer (D : Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (ddual : BinaryConjugationSection H QH HC ρ.dual)
    (ξ : Representation (ZMod 2) H Six)
    (dexterior : BinaryConjugationSection H VH UH ξ)
    (a : A) (ha : ∀ b, b ∈ zpowers a)
    (hnatural : ∀ v, ρ (inclusion (hAD.trans hDH) a) v = Matrix.mulVec planeCubic v)
    (hexterior : ∀ v, ξ (inclusion (hAD.trans hDH) a) v = exteriorMap planeCubic v)
    (f : D →* K) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (X : Subgroup K) [X.Normal] (hX : Nat.card X = 3)
    (hq : IsPGroup 2 (K ⧸ X)) (hAX : (A.subgroupOf D).map f = X)
    (Z U V C Q R : NormalNode D)
    (hZdef : Z.val = V1.subgroupOf D) (hUdef : U.val = UH.subgroupOf D)
    (hVdef : V.val = VH.subgroupOf D) (hCdef : C.val = HC.subgroupOf D)
    (hQdef : Q.val = QH.subgroupOf D)
    (hZ : IsCentral ⊥ Z) (hterminal : HasNoTwoChiefFactors (D ⧸ R.val))
    (Rg : Subgroup G) (hRdef : R.val = Rg.subgroupOf D) (hRg : IsPGroup 2 Rg)
    (τ : Representation (ZMod 2) D (Fin 4 → ZMod 2))
    (dradical : BinaryConjugationSection D Rg (QH ⊓ D) τ)
    (hradical : ∀ v, τ (inclusion hAD a) v = Matrix.mulVec pairedCubic v)
    (hnine : ∀ t : ChiefSeries D, t.head = ⊥ → t.last = ⊤ →
      9 ≤ t.noncentralTwoCount)
    (Kc Uγ : Subgroup G) (hKcH : Kc ≤ H) (hDK : D ≤ Kc)
    [IsElementaryAbelian 2 Uγ]
    (hQHdef : QH = H.pCoreIn 2)
    (hU : Nat.card Uγ = 32) (hstar : QH.relIndex Uγ = 2)
    (hintersection : 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G))
    (hcomm : ⁅HC,Uγ⁆ ≤ HC ⊓ Uγ) (hUγH : Uγ ≤ H)
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* BinaryLinear.OuterCyclic.LinearGroup 4)
    (hKc : IsPPerfect 2 Kc)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (Kc.subgroupOf H).subtype)) : False := by
  obtain ⟨hmove,hnotfour⟩ := source_chief_obstruction_of_cubic_sections
    H D UH V1 VH HC QH A hDH hAD hA hQH hVC hQHD ρ d ddual ξ dexterior
    a ha hnatural hexterior f hf hp X hX hq hAX Z U V C Q R
    hZdef hUdef hVdef hCdef hQdef hZ hterminal
    Rg hRdef hRg τ dradical hradical hnine Kc hKcH hDK
  exact linear_four_exclusion_of_chief_obstruction H QH HC VH Uγ Kc
    hQHdef hVC ddual.kernel_le
    ((normal_subgroupOf_iff_le_normalizer
      (ddual.kernel_le.trans ddual.section_le)).mp ddual.kernel_normal_actor)
    dexterior.normalized hU hstar hintersection hcomm hUγH hcover e
    hKcH hKc hmove hKonto (fun s hs0 hs1 _ => hnotfour s hs0 hs1)

end CFSG.Quasithin.Chapter13.Section08.LinearFour
