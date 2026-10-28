module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.NormalSeed.Recognition
public import Theory.GroupTheory.PerfectCenterPrimeRank
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.OrderNineAutomorphisms

/-!
# A normal elementary-nine seed excludes three from every C-component

Pass through the ambient two-core. Normality identifies the seed image
with its own two-core quotient, so this image has order nine and rank two.
Every perfect component centralizes it, since the automorphism group of
order nine is solvable. In A.3.6's simple and noncentral-Fitting cases the
component center has order prime to three, so prime ranks add. In the
triple-cover case central transfer forces component three-rank at least two;
the intersection with the seed has order at most three, again forcing
ambient rank at least three. Both contradict the SQTK rank bound.

All images use the original ambient quotient; odd rank is preserved when
lifting back. The source application is `normalSeedBender_of_parabolicSeed`.
Source: Aschbacher--Smith, 10.3.3, printed p.756, using A.3.6, pp.43--45.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender.NormalSeed
open Chapter1.Section02
universe u

private theorem normal_nine_centralized {H : Type*} [Group H] [Finite H]
    (A K : Subgroup H) [A.Normal] [Group.IsPerfect K] (hc : Nat.card A = 9) :
    K ≤ centralizer (A : Set H) := by
  let : Group.IsSolvable (MulAut A) := MulAut.isSolvable_of_card_nine hc
  let f : K →* MulAut A := (MulAut.conjNormal : H →* MulAut A).comp K.subtype
  have hf : f = 1 := by
    apply MonoidHom.range_eq_bot_iff.mp
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    by_contra hb
    let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hb
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro k hk a ha
  have he := congrArg (fun g : K →* MulAut A => ((g ⟨k,hk⟩ ⟨a,ha⟩ : A) : H)) hf
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem center_three_free_of_fitting {K : Type*} [Group K] [Finite K]
    (hc : Nat.Coprime 3 (Nat.card (generalizedFitting K))) :
    Nat.Coprime 3 (Nat.card (center K)) := by
  let : CommGroup (center K) := IsMulCommutative.instCommGroup
  have hz : center K ≤ fittingSubgroup K := le_sSup ⟨inferInstance,inferInstance⟩
  exact hc.coprime_dvd_right (card_dvd_of_le (hz.trans (fitting_le_generalizedFitting K)))

private theorem normal_nine_component_three_free
    {H : Type u} [Group H] [Finite H]
    (hr : primeRank 3 H ≤ 2) (A : Subgroup H) [A.Normal]
    (hc : Nat.card A = 9) (ha : 2 ≤ primeRank 3 A)
    (K : Subgroup H) (hK : K.IsCComponent) (hm : A36Conclusion K) :
    ¬ 3 ∣ Nat.card K := by
  let := hK.perfect
  have hcomm : A ≤ centralizer (K : Set H) :=
    le_centralizer_iff.mp (normal_nine_centralized A K hc)
  have of_center (hz : Nat.Coprime 3 (Nat.card (center K))) : ¬3 ∣ Nat.card K := by
    have hh := ResidualCentralizerRank.primeRank_add_le_of_center_coprime A K hcomm hz
    have hz0 : primeRank 3 K = 0 := by omega
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz0
  cases hm.1 with
  | simple hcomponent hs _ =>
    let := hs
    apply of_center
    have hz : center K = ⊥ := by
      rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · exact (hK.not_isSolvable (Group.isSolvable_of_comm fun x y =>
          (mem_center_iff.mp (ht ▸ mem_top x) y).symm)).elim
    rw [hz, card_bot]
    decide
  | cover hcomponent he _ =>
    obtain ⟨e⟩ := he
    have hz : Nat.card (center K) = 3 := by rw [Nat.card_congr e.toEquiv]; simp
    have hrK : 2 ≤ primeRank 3 K :=
      two_le_primeRank_of_nontrivial_prime_center (by decide : Odd 3)
        (IsPGroup.of_card (n := 1) (by simpa using hz))
        (by intro hb; rw [hb,card_bot] at hz; omega)
    have hi : Nat.card (A ⊓ K : Subgroup H) ≤ 3 := by
      let f : (A ⊓ K : Subgroup H) →* center K :=
        { toFun := fun x => ⟨⟨x,x.property.2⟩, mem_center_iff.mpr fun k =>
            Subtype.ext (hcomm x.property.1 k k.property)⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hf : Function.Injective f := fun x y he =>
        Subtype.ext (congrArg (fun z : center K => ((z : K) : H)) he)
      exact hz ▸ Nat.card_le_card_of_injective f hf
    have hh := three_le_primeRank_of_cubic_intersection A K hcomm hi ha hrK
    omega
  | natural hn =>
    apply of_center
    apply center_three_free_of_fitting
    obtain ⟨p,hp,hlarge,F,_,_,hF,e,_,_⟩ := hn.2
    rw [Nat.card_congr e.toEquiv]
    change Nat.Coprime 3 (Nat.card (Fin 2 → F))
    rw [Nat.card_fun,Nat.card_fin,hF]
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr
      (fun hd => (hp.eq_one_or_self_of_dvd 3 hd).elim (by decide) (by omega))).pow_right 2
  | nilpotent hn =>
    apply of_center
    apply center_three_free_of_fitting
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hh := (hn.2.2.2 3 (by decide) hd).1
    norm_num at hh

/-- The intrinsic normal-seed rank obstruction. -/
theorem normalNineRank {H : Type u} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (X : Subgroup H) [X.Normal]
    (he : Nonempty ((X ⧸ pCore 2 X) ≃* Multiplicative (Fin 2 → ZMod 3)))
    (I : Subgroup H) (hI : I.IsCComponent) : ¬ 3 ∣ Nat.card I := by
  let Q := H ⧸ pCore 2 H
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := X.map q
  let K := I.map q
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let f := q.subgroupMap X
  have hk : f.ker = pCore 2 X := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 (inferInstance : X.Normal).isSubnormal).symm
  let e : A ≃* Multiplicative (Fin 2 → ZMod 3) :=
    ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective X))).symm.trans he.some
  have hc : Nat.card A = 9 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Fin 2 → ZMod 3) = 9
    simp
  have hpow (a : Multiplicative (Fin 2 → ZMod 3)) : a ^ 3 = 1 := by
    change (3 : ℕ) • (Multiplicative.toAdd a) = 0
    ext i
    exact ZModModule.char_nsmul_eq_zero 3 (Multiplicative.toAdd a i)
  have ha : 2 ≤ primeRank 3 A := by
    exact primeRank_ge_of_elementary_embedding hpow (by simp)
      e.symm.toMonoidHom e.symm.injective
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  have hm := proposition_1_2_1_four_earlier_conclusion
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hQ hI
  have hn := normal_nine_component_three_free
    (hQ.stronglyQuasithin 3 (by decide) (by decide)) A hc ha K (hI.map_quotient _) hm
  have hr : primeRank 3 K = primeRank 3 I :=
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) I
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp
    (hr ▸ PrimeRank.eq_zero_iff_not_dvd_card.mpr hn)

/-- The exact rank contract, retaining normality in the local ambient group. -/
theorem normalNineRankInput : NormalNineRankInput.{u} := by
  intro H _ _ hH X hX he I hI
  let := hX
  exact normalNineRank hH X he I hI

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender.NormalSeed
