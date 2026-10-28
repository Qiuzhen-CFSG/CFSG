module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceCommonCubic
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.ComplementAccounting
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.CubicObstruction

/-!
# Applying the compatible cubic to the terminal chief obstruction

The common scalar cubic fixes the marked V₃/V₁ plane. Its action on the
literal upper-right radical is right multiplication by the inverse cubic,
so its coordinate matrix differs from the one rotating the first plane.
The radical coordinate identity determines this action without changing
any subgroup, kernel or quotient map. The four surrounding sections then
leave three noncentral factors on H_C/V_H. Restriction rules out a unique
factor of order sixteen, and the actual H/O₂(H) section argument supplies
the conditional terminal contradiction.

This is a source-compatible replacement when retaining the original tensor
point and plane coordinates. The nine-factor lower bound, original natural
and exterior markings and critical geometry remain explicit obligations of
qt-d-138-linear-four-source. The prior 13.8.27 setup belongs to
qt-d-138-six-g2-source; qt-d-1381-source owns final assembly. These results
do not establish the full 13.8.28.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
13.8.31 and the proof of 13.8.28, printed pp.965–966.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare PlaneSpan
variable {G : Type*} [Group G] [Finite G]

/-- The literal cubic section calculations supply both clauses of the
13.8.31(3) obstruction consumed by the terminal H-chief-series argument. -/
theorem source_chief_obstruction_of_complement_sections
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
    (hnatural : ∀ v, ρ (inclusion (hAD.trans hDH) a) v = Matrix.mulVec complementCubic v)
    (hexterior : ∀ v, ξ (inclusion (hAD.trans hDH) a) v = exteriorMap complementCubic v)
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
    (hradical : ∀ v, τ (inclusion hAD a) v = Matrix.mulVec complementRadicalCubic v)
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
    source_three_factors_of_complement_sections H D UH V1 VH HC QH A hDH hAD hA
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
theorem source_linear_four_exclusion_of_complement_sections
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
    (hnatural : ∀ v, ρ (inclusion (hAD.trans hDH) a) v = Matrix.mulVec complementCubic v)
    (hexterior : ∀ v, ξ (inclusion (hAD.trans hDH) a) v = exteriorMap complementCubic v)
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
    (hradical : ∀ v, τ (inclusion hAD a) v = Matrix.mulVec complementRadicalCubic v)
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
  obtain ⟨hmove,hnotfour⟩ := source_chief_obstruction_of_complement_sections
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

/-- The common actor and radical action are derived from the original matrix quotient. -/
theorem source_linear_four_exclusion_of_complement_matrices
    {K : Type*} [Group K] [Finite K]
    (H D UH V1 VH HC QH : Subgroup G) (hDH : D ≤ H) (hQH : IsPGroup 2 QH) (hVC : VH ≤ HC)
    (hQHD : QH ≤ normalizer (D : Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (ddual : BinaryConjugationSection H QH HC ρ.dual)
    (ξ : Representation (ZMod 2) H Six)
    (dexterior : BinaryConjugationSection H VH UH ξ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h v, ρ h v = Matrix.mulVec (π h).val v)
    (hexterior : ∀ h v, ξ h v = exteriorMap (π h).val v)
    (hcubic : complementElement ∈ (D.subgroupOf H).map π)
    (f : D →* K) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (X : Subgroup K) [X.Normal] (hX : Nat.card X = 3)
    (hq : IsPGroup 2 (K ⧸ X))
    (Z U V C Q R : NormalNode D)
    (hZdef : Z.val = V1.subgroupOf D) (hUdef : U.val = UH.subgroupOf D)
    (hVdef : V.val = VH.subgroupOf D) (hCdef : C.val = HC.subgroupOf D)
    (hQdef : Q.val = QH.subgroupOf D)
    (hZ : IsCentral ⊥ Z) (hterminal : HasNoTwoChiefFactors (D ⧸ R.val))
    (Rg : Subgroup G) (hRdef : R.val = Rg.subgroupOf D) (hRg : IsPGroup 2 Rg)
    (hRD : Rg ≤ D) (hQR : QH ⊓ D ≤ Rg)
    (hradical : (Rg.subgroupOf H).map π = PlaneRadical.radical)
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
  obtain ⟨A,hAD,a,hA,ha,hmat⟩ := source_common_complement_cubic H D QH hDH hQH π hker hcubic
  have hAc : Nat.card (A.subgroupOf D) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv).trans hA
  have hAX := cubic_image_eq_normal_three f hp (A.subgroupOf D) hAc X hX hq
  have hDR : D ≤ normalizer (Rg : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hRD).mp
    rw [←hRdef]
    exact R.property
  obtain ⟨τ,dradical,hcoordinates,_⟩ := PlaneRadical.exists_section H D Rg QH hDH hRD hDR hQR π hker hradical
  exact source_linear_four_exclusion_of_complement_sections
    H D UH V1 VH HC QH A hDH hAD hA hQH hVC hQHD ρ d ddual ξ dexterior
    a ha (fun v => (hnatural _ v).trans (by rw [hmat]))
    (fun v => (hexterior _ v).trans (by rw [hmat]))
    f hf hp X hX hq hAX Z U V C Q R hZdef hUdef hVdef hCdef hQdef hZ hterminal
    Rg hRdef hRg τ dradical (section_complement_action H D Rg (QH ⊓ D) hDH hRD π τ dradical
      hcoordinates (inclusion hAD a) hmat) hnine
    Kc Uγ hKcH hDK hQHdef hU hstar hintersection hcomm hUγH hcover e hKc hKonto

end CFSG.Quasithin.Chapter13.Section08.LinearFour
