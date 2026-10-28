module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.RootClasses
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.SuzukiRadical
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus

/-!
# A coordinate reduction for Ree involutions

Every involution in the positive Ree subgroup has a unique positive-root word.
Its square forces the first Suzuki-Levi main coordinate to vanish. Projection
to the Suzuki Levi quotient then factors the involution as the central curve
`y₁(t)` times an element of the Suzuki radical. Conjugating an arbitrary
involution into the positive Sylow gives the same reduction for every native
involution of `Model m`.

This is a coordinate reduction only; it does not identify the resulting
conjugacy class or prove exhaustion by the long- and short-root classes.
Source: Aschbacher–Smith F.4.27(3), printed p.288 of `refs/quasithin.pdf`.
The positive coordinates and the Suzuki quotient use the actual fixed Ree
matrix carrier and retain all `m > 0`.
-/

public noncomputable section
namespace ReeF4.SourceCompletion
open Subgroup Parabolics LargeLocalSeeds
open NormalizedRootCentralizers.CenterExponent
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations MatrixRelations.LongCommutators OuterElimination
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open ElementaryTwoBound.RootCalculations
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem


private theorem first_root_mem_levi (m : ℕ) (i : Fin 24) (hi : i.val < 4)
    (t : CoefficientField m) : X m i t ∈ splitLevi m .suzuki := by
  apply (show splitSimpleBlock m .suzuki true ≤ splitLevi m .suzuki from le_sup_left)
  apply Subgroup.subset_closure
  refine ⟨R i,t,⟨?_,rpos i⟩,by unfold X; rfl⟩
  intro j hj
  rw [rval]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  all_goals fin_cases j
  all_goals simp_all [leviNodes, typeF4SimpleCoefficient, V]

private theorem first_central_injective (m : ℕ) : Function.Injective (centralWord m 0) := by
  intro a b h
  have hc (t : CoefficientField m) :
      centralWord m 0 t = splitWord m ![0,0,halfFrobenius m t,t,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
    have hf : rootFieldEnd m (longRoot 0) = halfFrobenius m := by
      simp only [rootFieldEnd, if_pos (longRoot_isLong 0), halfFrobenius]
    simp only [splitWord, Matrix.cons_val_zero, Matrix.cons_val,
      xz, one_mul, mul_one]
    simp only [centralWord,hf]
    change rootGeneratorInGroup m (R 3) t * rootGeneratorInGroup m (R 2) (halfFrobenius m t) = _
    rw [←show X m 3 t = rootGeneratorInGroup m (R 3) t from rfl,
      ←show X m 2 (halfFrobenius m t) = rootGeneratorInGroup m (R 2) (halfFrobenius m t) from rfl]
    exact (xc m 3 2 (by norm_num [V,dot,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three]) _ _).eq
  rw [hc,hc] at h
  exact congrFun (splitWord_injective m h) 3

private theorem first_main_central_commute (m : ℕ) (a c : CoefficientField m) :
    Commute (rootWord m 0 a) (centralWord m 0 c) := by
  have hf : rootFieldEnd m (longRoot 0) = halfFrobenius m := by
    simp only [rootFieldEnd, if_pos (longRoot_isLong 0), halfFrobenius]
  simp only [rootWord,centralWord,hf, show (0 : Fin 8).val % 2 = 0 from rfl, ite_true]
  change Commute (X m 0 a * X m 1 (halfFrobenius m a) * X m 2 (a*halfFrobenius m a))
    (X m 3 c * X m 2 (halfFrobenius m c))
  have h (i j : Fin 24) (hij : dot (V i) (V j) ≥ 0) (a b : CoefficientField m) := xc m i j hij a b
  apply Commute.mul_left
  · apply Commute.mul_left
    · exact (h 0 3 (by norm_num [V,dot,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three]) _ _).mul_right
        (h 0 2 (by norm_num [V,dot,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three]) _ _)
    · exact (h 1 3 (by norm_num [V,dot,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three]) _ _).mul_right
        (h 1 2 (by norm_num [V,dot,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three]) _ _)
  · exact (h 2 3 (by norm_num [V,dot,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three]) _ _).mul_right (by
          change X m 2 _ * X m 2 _ = _
          rw [xa,xa]
          exact congrArg (X m 2) (add_comm _ _))

private theorem first_word_square (m : ℕ) (a c : CoefficientField m) :
    (rootWord m 0 a * centralWord m 0 c)^2 = centralWord m 0 (titsEnd m a * a) := by
  rw [(first_main_central_commute m a c).mul_pow]
  have hc : centralWord m 0 c ^ 2 = 1 := by
    have h := congrArg (toSplitGroup m) (show ElementaryTwoBound.centralElement m 0 c ^ 2 = 1 from by
      rw [pow_two,←centralElement_add m 0 (by decide),CharTwo.add_self_eq_zero,centralElement_zero])
    simpa only [map_pow,map_one,ElementaryTwoBound.centralElement_coe] using h
  rw [hc,mul_one,pow_two,rootWord_even_mul m 0 (by decide),CharTwo.add_self_eq_zero,
    rootWord_zero,one_mul]

private theorem first_word_mem_levi (m : ℕ) (a c : CoefficientField m) :
    rootWord m 0 a * centralWord m 0 c ∈ splitLevi m .suzuki := by
  simp only [rootWord,centralWord,show (0 : Fin 8).val % 2 = 0 from rfl, ite_true]
  change X m 0 a * X m 1 (rootFieldEnd m (longRoot 0) a) *
    X m 2 (a*rootFieldEnd m (longRoot 0) a) *
    (X m 3 c * X m 2 (rootFieldEnd m (longRoot 0) c)) ∈ splitLevi m .suzuki
  exact mul_mem (mul_mem (mul_mem (first_root_mem_levi m 0 (by decide) _)
    (first_root_mem_levi m 1 (by decide) _)) (first_root_mem_levi m 2 (by decide) _))
    (mul_mem (first_root_mem_levi m 3 (by decide) _) (first_root_mem_levi m 2 (by decide) _))

private theorem central_mem_suzuki_radical (m : ℕ) (i : Fin 8)
    (hi : i ≠ 0) (he : i.val % 2 = 0) (t : CoefficientField m) :
    ElementaryTwoBound.centralElement m i t ∈ radical m .suzuki := by
  have hl : ElementaryTwoBound.X m i ≤ radical m .suzuki := by
    apply (Subgroup.closure_le _).2
    rintro x ⟨a,rfl⟩
    exact mainElement_mem_suzuki_radical m i hi a
  exact hl (Y_le_X m i he (centralElement_mem_Y m i t))

private def firstQuotient (m : ℕ) :=
  (splitSeed m .suzuki) ⧸ radicalInSplitSeed m .suzuki

private instance (m : ℕ) : Group (firstQuotient m) := by
  let := radicalInSplitSeed_normal m .suzuki
  exact QuotientGroup.Quotient.group _

private def firstProjection (m : ℕ) : unipotent m →* firstQuotient m := by
  let := radicalInSplitSeed_normal m .suzuki
  exact (QuotientGroup.mk' (radicalInSplitSeed m .suzuki)).comp
    ((toSplitGroup m).comp (unipotent m).subtype |>.codRestrict
      (splitSeed m .suzuki) (fun x => splitUnipotent_le_splitSeed m .suzuki x.property))

private theorem firstProjection_eq_one (m : ℕ) (x : unipotent m)
    (hx : x.val ∈ radical m .suzuki) : firstProjection m x = 1 := by
  let := radicalInSplitSeed_normal m .suzuki
  exact (QuotientGroup.eq_one_iff _).mpr hx

private def firstElement (m : ℕ) (a c : CoefficientField m) : Model m :=
  mainElement m 0 a * ElementaryTwoBound.centralElement m 0 c

private theorem firstElement_mem (m : ℕ) (a c : CoefficientField m) :
    firstElement m a c ∈ unipotent m :=
  mul_mem (mainElement_mem_unipotent m 0 a)
    (by
      change toSplitGroup m (ElementaryTwoBound.centralElement m 0 c) ∈ splitUnipotent m
      rw [ElementaryTwoBound.centralElement_coe]
      exact (positive_words_fixed_mem m 0 c).2.2)

private theorem firstProjection_positiveWord (m : ℕ) (x : unipotent m)
    (p : PositiveParameters m) (hp : toSplitGroup m x.val = positiveWord m p) :
    firstProjection m x = firstProjection m
      ⟨firstElement m (p.main 0) (p.central 0),firstElement_mem m _ _⟩ := by
  let f := firstProjection m
  let u (i : Fin 8) (a : CoefficientField m) : unipotent m :=
    ⟨mainElement m i a,mainElement_mem_unipotent m i a⟩
  let v (i : Fin 8) (a : CoefficientField m) : unipotent m :=
    ⟨ElementaryTwoBound.centralElement m i a,by
      change toSplitGroup m (ElementaryTwoBound.centralElement m i a) ∈ splitUnipotent m
      rw [ElementaryTwoBound.centralElement_coe]
      exact (positive_words_fixed_mem m i a).2.2⟩
  have hu (i : Fin 8) (hi : i ≠ 0) (a : CoefficientField m) : f (u i a) = 1 :=
    firstProjection_eq_one m _ (mainElement_mem_suzuki_radical m i hi a)
  have hv (i : Fin 8) (hi : i ≠ 0) (he : i.val % 2 = 0) (a : CoefficientField m) :
      f (v i a) = 1 :=
    firstProjection_eq_one m _ (central_mem_suzuki_radical m i hi he a)
  have hx : x =
      (u 7 (p.pair 0) * u 1 (p.pair 1) * u 5 (p.pair 2) * u 3 (p.pair 3)) *
      ((u 0 (p.main 0) * v 0 (p.central 0)) *
       (u 4 (p.main 1) * v 4 (p.central 1)) *
       (u 6 (p.main 2) * v 6 (p.central 2)) *
       (u 2 (p.main 3) * v 2 (p.central 3))) := by
    apply Subtype.ext
    have he : x.val = wordElement m p :=
      toSplitGroup_injective m (hp.trans (wordElement_coe m p).symm)
    rw [he]
    simp [wordElement,positive_pair_indices,positive_quartet_indices,
      pairCount,quartetCount,List.ofFn_succ,u,v,mul_assoc]
  change f x = f (u 0 (p.main 0) * v 0 (p.central 0))
  rw [hx]
  simp only [map_mul,hu 7 (by decide),hu 1 (by decide),hu 5 (by decide),hu 3 (by decide),
    hu 4 (by decide),hu 6 (by decide),hu 2 (by decide),
    hv 4 (by decide) (by decide),hv 6 (by decide) (by decide),hv 2 (by decide) (by decide),
    one_mul,mul_one]

/-- The first noncentral Suzuki coordinate of any square-one positive word is zero. -/
theorem positive_involution_first_main_zero (m : ℕ) (x : unipotent m)
    (p : PositiveParameters m) (hp : toSplitGroup m x.val = positiveWord m p)
    (hs : x.val ^ 2 = 1) : p.main 0 = 0 := by
  let := radicalInSplitSeed_normal m .suzuki
  have hs' : x ^ 2 = 1 := Subtype.ext hs
  have hq : firstProjection m x ^ 2 = 1 := by rw [←map_pow,hs',map_one]
  rw [firstProjection_positiveWord m x p hp,←map_pow] at hq
  have hr' := (QuotientGroup.eq_one_iff
    (N := radicalInSplitSeed m .suzuki) _).mp hq
  have hr : toSplitGroup m (firstElement m (p.main 0) (p.central 0)) ^ 2 ∈
      splitRadical m .suzuki := by
    change toSplitGroup m ((firstElement m (p.main 0) (p.central 0))^2) ∈ splitRadical m .suzuki at hr'
    simpa only [map_pow] using hr'
  have he : toSplitGroup m (firstElement m (p.main 0) (p.central 0)) =
      rootWord m 0 (p.main 0) * centralWord m 0 (p.central 0) := by
    simp only [firstElement,map_mul,mainElement_coe,ElementaryTwoBound.centralElement_coe]
  rw [he] at hr
  have hl := (splitLevi m .suzuki).pow_mem
    (first_word_mem_levi m (p.main 0) (p.central 0)) 2
  have hone : (rootWord m 0 (p.main 0) * centralWord m 0 (p.central 0)) ^ 2 = 1 :=
    Subgroup.mem_bot.mp ((splitLevi_disjoint_splitRadical m .suzuki).le_bot ⟨hl,hr⟩)
  rw [first_word_square] at hone
  have hz : titsEnd m (p.main 0) * p.main 0 = 0 :=
    first_central_injective m (hone.trans (centralWord_zero m 0).symm)
  rcases mul_eq_zero.mp hz with hz | hz
  · exact (titsEnd m).injective (by simpa only [map_zero] using hz)
  · exact hz

/-- Every square-one positive element has central Suzuki-Levi factor. -/
theorem positive_involution_suzuki_factor (m : ℕ) (x : unipotent m)
    (hs : x.val ^ 2 = 1) :
    ∃ (p : PositiveParameters m) (r : radical m .suzuki),
      toSplitGroup m x.val = positiveWord m p ∧ p.main 0 = 0 ∧
      x.val = ElementaryTwoBound.centralElement m 0 (p.central 0) * r.val := by
  obtain ⟨p,hp⟩ := exists_positiveWord m x.val x.property
  have hm0 := positive_involution_first_main_zero m x p hp hs
  let z : unipotent m := ⟨firstElement m 0 (p.central 0),firstElement_mem m _ _⟩
  have hz : z.val = ElementaryTwoBound.centralElement m 0 (p.central 0) := by
    simp only [z,firstElement,mainElement_zero,one_mul]
  have hproj : firstProjection m x = firstProjection m z := by
    rw [firstProjection_positiveWord m x p hp,hm0]
  let r := z⁻¹*x
  have hqr : firstProjection m r = 1 := by
    simp only [r,map_mul,map_inv,hproj,inv_mul_cancel]
  let := radicalInSplitSeed_normal m .suzuki
  have hr : r.val ∈ radical m .suzuki :=
    (QuotientGroup.eq_one_iff (N := radicalInSplitSeed m .suzuki) _).mp hqr
  refine ⟨p,⟨r.val,hr⟩,hp,hm0,?_⟩
  rw [←hz]
  exact (congrArg Subtype.val (mul_inv_cancel_left z x)).symm

/-- Every native involution is conjugate to a positive word with only a
central factor in the first Suzuki Levi. The remaining radical factor is literal. -/
theorem involution_suzuki_normal_form (m : ℕ) (x : Model m) (hx : orderOf x = 2) :
    ∃ (g : Model m) (p : PositiveParameters m) (r : radical m .suzuki),
      p.main 0 = 0 ∧
      toSplitGroup m ((MulAut.conj g) x) = positiveWord m p ∧
      (MulAut.conj g) x = ElementaryTwoBound.centralElement m 0 (p.central 0) * r.val := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  obtain ⟨U,hU⟩ := ConverseParabolics.exists_sylow_eq_unipotent m
  have hU' : (U : Subgroup (Model m)) = unipotent m :=
    hU.trans (MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.unipotent_eq_rootUnipotent m)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model m) S U
  have hyU : (MulAut.conj g) x ∈ unipotent m := by
    rw [←hU',←hg]
    exact ⟨x,hS (mem_zpowers x),rfl⟩
  have hy2 : ((MulAut.conj g) x)^2 = 1 := by
    have hx2 : x^2 = 1 := (orderOf_eq_prime_iff.mp hx).1
    rw [←map_pow,hx2,map_one]
  obtain ⟨p,r,hp,h0,hr⟩ := positive_involution_suzuki_factor m
    ⟨(MulAut.conj g) x,hyU⟩ hy2
  exact ⟨g,p,r,h0,hp,hr⟩
/-- Every Borel involution lies in the literal positive Sylow. This permits
the coordinate reduction on a marked element itself, without conjugating it. -/
theorem involution_mem_unipotent_of_mem_borel (m : ℕ) (x : Model m) (hxB : x ∈ borel m) (hx : orderOf x = 2) :
    x ∈ unipotent m := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  obtain ⟨U,hU⟩ := ConverseParabolics.exists_sylow_eq_unipotent m
  have hU' : (U : Subgroup (Model m)) = unipotent m :=
    hU.trans (MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.unipotent_eq_rootUnipotent m)
  have hxN : x ∈ normalizer (U : Set (Model m)) := by
    change x ∈ normalizer ((U : Subgroup (Model m)) : Set (Model m))
    rw [hU',unipotent_normalizer_eq_borel]
    exact hxB
  have hm : x ∈ zpowers x ⊓ normalizer (U : Set (Model m)) := ⟨mem_zpowers x,hxN⟩
  rw [hp.inf_normalizer_sylow U] at hm
  exact hU' ▸ hm.2

end ReeF4.SourceCompletion
