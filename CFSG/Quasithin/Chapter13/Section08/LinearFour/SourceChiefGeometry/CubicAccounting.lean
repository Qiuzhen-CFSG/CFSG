module

public import Theory.Representation.BinaryParabolicExteriorSquare.CubicRestriction
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Intervals
public import Theory.Representation.BinaryConjugationSection.CubicLength
public import Theory.Representation.BinaryConjugationSection.tensorChief

/-!
# The six surrounding chief factors from the actual cubic actions

The common cubic has fixed indices four, sixteen and four on the natural,
exterior and dual sections U_H/V₁, V_H/U_H and Q_H/H_C. The paired radical
action has fixed index sixteen. Coprime fixed-point lifting carries these
calculations to the literal intersections with L₀. The cubic chief-count
theorem gives their counts 1, 2, 1 and 2 without homogeneous-filtration
witnesses. Refining the central bottom and terminal odd quotient and
inserting an arbitrary chief series in H_C/V_H proves that the nine-factor
lower bound leaves at least three noncentral factors in that interval.

The representations and their single-cubic markings, the normalizer
geometry, the upper radical section and the nine-factor lower bound remain
explicit. They must be constructed from the genuine source setup by
qt-d-138-linear-four-source; the earlier 13.8.27 setup belongs to
qt-d-138-six-g2-source, and qt-d-1381-source owns final assembly.
This calculation alone does not establish 13.8.28 or all of 13.8.31.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), 13.8.31(3), printed p.965.
-/

public section
open Subgroup Representation NoncentralChiefRefinement
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare.PlaneSpan
variable {G : Type*} [Group G] [Finite G]

/-- The same cubic on the natural, exterior and contragredient sections has
literal section lengths one, two and one. -/
theorem source_natural_exterior_dual_cubic_lengths
    (H UH V1 VH HC QH A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 3)
    (hQH : IsPGroup 2 QH) (hVC : VH ≤ HC)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (ddual : BinaryConjugationSection H QH HC ρ.dual)
    (ξ : Representation (ZMod 2) H Six)
    (dexterior : BinaryConjugationSection H VH UH ξ)
    (a : A) (ha : ∀ b, b ∈ zpowers a)
    (hnatural : ∀ v, ρ (inclusion hAH a) v = Matrix.mulVec planeCubic v)
    (hexterior : ∀ v, ξ (inclusion hAH a) v = exteriorMap planeCubic v) :
    sectionCubicLength A V1 UH = 1 ∧ sectionCubicLength A UH VH = 2 ∧
      sectionCubicLength A HC QH = 1 := by
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hVH : IsPGroup 2 VH := hQH.to_le (hVC.trans ddual.kernel_le)
  have hUH : IsPGroup 2 UH := hVH.to_le dexterior.kernel_le
  have hn : sectionCubicLength A V1 UH = 1 := by
    rw [d.sectionCubicLength_eq_fixedIndex A hAH hAp hUH,
      natural_cubic_fixedIndex (ρ.comp (inclusion hAH)) a ha hnatural]
    decide
  refine ⟨hn, ?_, ?_⟩
  · rw [dexterior.sectionCubicLength_eq_fixedIndex A hAH hAp hVH,
      exterior_cubic_fixedIndex (ξ.comp (inclusion hAH)) a ha hexterior]
    decide
  · rw [ddual.sectionCubicLength_eq_fixedIndex A hAH hAp hQH]
    change Nat.log 4 (BinaryFixedPoints.fixedIndex (Representation.dual (ρ.comp (inclusion hAH)))) = 1
    rw [dual_natural_cubic_fixedIndex (ρ.comp (inclusion hAH)) a ha hnatural]
    decide

/-- Three surrounding chief counts follow from the actual section actions
and normalizer geometry; no homogeneous-stratum witnesses are assumed. -/
theorem source_three_cubic_chief_counts
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
    (s₁ s₂ s₃ : ChiefSeries D)
    (hs₁0 : s₁.head.val = V1.subgroupOf D) (hs₁1 : s₁.last.val = UH.subgroupOf D)
    (hs₂0 : s₂.head.val = UH.subgroupOf D) (hs₂1 : s₂.last.val = VH.subgroupOf D)
    (hs₃0 : s₃.head.val = HC.subgroupOf D) (hs₃1 : s₃.last.val = QH.subgroupOf D) :
    s₁.noncentralTwoCount = 1 ∧ s₂.noncentralTwoCount = 2 ∧ s₃.noncentralTwoCount = 1 := by
  obtain ⟨hn,he,hd⟩ := source_natural_exterior_dual_cubic_lengths H UH V1 VH HC QH A
    (hAD.trans hDH) hA hQH hVC ρ d ddual ξ dexterior a ha hnatural hexterior
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hVQ := hVC.trans ddual.kernel_le
  have hUQ := dexterior.kernel_le.trans hVQ
  have h1Q := d.kernel_le.trans hUQ
  refine ⟨?_,?_,?_⟩
  · exact (CubicComparison.intersection_interval_count D A V1 UH hAD hAp
      (hQH.to_le h1Q) (hQH.to_le hUQ) (h1Q.trans hQHD) (hUQ.trans hQHD)
      (hDH.trans ((normal_subgroupOf_iff_le_normalizer (d.kernel_le.trans d.section_le)).mp d.kernel_normal_actor)) (hDH.trans d.normalized)
      f hf hp X hX hq hAX s₁ hs₁0 hs₁1).trans hn
  · exact (CubicComparison.intersection_interval_count D A UH VH hAD hAp
      (hQH.to_le hUQ) (hQH.to_le hVQ) (hUQ.trans hQHD) (hVQ.trans hQHD)
      (hDH.trans d.normalized) (hDH.trans dexterior.normalized)
      f hf hp X hX hq hAX s₂ hs₂0 hs₂1).trans he
  · exact (CubicComparison.intersection_interval_count D A HC QH hAD hAp
      (hQH.to_le ddual.kernel_le) hQH (ddual.kernel_le.trans hQHD) hQHD
      (hDH.trans ((normal_subgroupOf_iff_le_normalizer (ddual.kernel_le.trans ddual.section_le)).mp ddual.kernel_normal_actor)) (hDH.trans ddual.normalized)
      f hf hp X hX hq hAX s₃ hs₃0 hs₃1).trans hd

end CFSG.Quasithin.Chapter13.Section08.LinearFour

public section
open Subgroup Representation NoncentralChiefRefinement
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare.PlaneSpan
variable {G : Type*} [Group G] [Finite G]

/-- The natural, exterior, dual and radical actions produce the six
surrounding chief factors, leaving three on the literal H_C/V_H intersection.
No chief multiplicity or homogeneous filtration is an input. -/
theorem source_three_factors_of_cubic_sections
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
    (s : ChiefSeries D) (hs0 : s.head = V) (hs1 : s.last = C) :
    3 ≤ s.noncentralTwoCount := by
  have hZU : Z ≤ U := by
    change Z.val ≤ U.val
    rw [hZdef,hUdef]
    exact subgroupOf_mono D d.kernel_le
  have hUV : U ≤ V := by
    change U.val ≤ V.val
    rw [hUdef,hVdef]
    exact subgroupOf_mono D dexterior.kernel_le
  have hCQ : C ≤ Q := by
    change C.val ≤ Q.val
    rw [hCdef,hQdef]
    exact subgroupOf_mono D ddual.kernel_le
  obtain ⟨s₁,h10,h11⟩ := exists_chiefSeries Z U hZU
  obtain ⟨s₂,h20,h21⟩ := exists_chiefSeries U V hUV
  obtain ⟨s₃,h30,h31⟩ := exists_chiefSeries C Q hCQ
  obtain ⟨hc1,hc2,hc3⟩ := source_three_cubic_chief_counts H D UH V1 VH HC QH A
    hDH hAD hA hQH hVC hQHD ρ d ddual ξ dexterior a ha hnatural hexterior
    f hf hp X hX hq hAX s₁ s₂ s₃
    ((congrArg Subtype.val h10).trans hZdef) ((congrArg Subtype.val h11).trans hUdef)
    ((congrArg Subtype.val h20).trans hUdef) ((congrArg Subtype.val h21).trans hVdef)
    ((congrArg Subtype.val h30).trans hCdef) ((congrArg Subtype.val h31).trans hQdef)
  have hQR : Q ≤ R := by
    change Q.val ≤ R.val
    rw [hQdef,hRdef]
    intro x hx
    exact dradical.kernel_le ⟨hx,x.property⟩
  obtain ⟨s₄,h40,h41⟩ := exists_chiefSeries Q R hQR
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hrad : sectionCubicLength A (QH ⊓ D) Rg = 2 := by
    rw [dradical.sectionCubicLength_eq_fixedIndex A hAD hAp hRg,
      paired_cubic_fixedIndex (τ.comp (inclusion hAD)) a ha hradical]
    decide
  have hc4 : s₄.noncentralTwoCount = 2 := by
    apply (CubicComparison.intersection_interval_count D A (QH ⊓ D) Rg hAD hAp
      (hQH.to_le inf_le_left) hRg (inf_le_right.trans D.le_normalizer)
      (dradical.section_le.trans D.le_normalizer)
      ((normal_subgroupOf_iff_le_normalizer
        (dradical.kernel_le.trans dradical.section_le)).mp dradical.kernel_normal_actor)
      dradical.normalized f hf hp X hX hq hAX s₄ ?_ ?_).trans hrad
    · rw [h40,hQdef]
      ext x
      exact ⟨fun hx => ⟨hx,x.property⟩, fun hx => hx.1⟩
    · exact (congrArg Subtype.val h41).trans hRdef
  obtain ⟨z,hz0,hz1⟩ := exists_chiefSeries (⊥ : NormalNode D) Z bot_le
  have hzc : z.noncentralTwoCount = 0 :=
    z.noncentralTwoCount_eq_zero_of_central (by rwa [hz0,hz1])
  obtain ⟨r,hr0,hr1⟩ := exists_chiefSeries R (⊤ : NormalNode D) le_top
  have hrc : r.noncentralTwoCount = 0 :=
    r.noncentralTwoCount_eq_zero_of_quotient R hr0.ge hterminal
  let z1 := z.smash s₁ (hz1.trans h10.symm)
  let z12 := z1.smash s₂ ((RelSeries.last_smash _).trans (h11.trans h20.symm))
  let z12s := z12.smash s ((RelSeries.last_smash _).trans (h21.trans hs0.symm))
  let z12s3 := z12s.smash s₃ ((RelSeries.last_smash _).trans (hs1.trans h30.symm))
  let z12s34 := z12s3.smash s₄ ((RelSeries.last_smash _).trans (h31.trans h40.symm))
  let t := z12s34.smash r ((RelSeries.last_smash _).trans (h41.trans hr0.symm))
  have ht0 : t.head = ⊥ := by
    simp only [t,z12s34,z12s3,z12s,z12,z1,RelSeries.head_smash,hz0]
  have ht1 : t.last = ⊤ := (RelSeries.last_smash _).trans hr1
  have ht := hnine t ht0 ht1
  simp only [t,z12s34,z12s3,z12s,z12,z1,ChiefSeries.noncentralTwoCount_smash,
    hzc,hrc,hc1,hc2,hc3,hc4] at ht
  omega

end CFSG.Quasithin.Chapter13.Section08.LinearFour
