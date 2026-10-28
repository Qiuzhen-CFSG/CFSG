module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.ModelExclusions
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Outer
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.Held
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.SevenExclusion
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M24Table.TwoAKernel
public import Theory.Mathieu.M22.Properties.OuterCentralizers.SevenExclusion
public import Theory.Mathieu.M22.Properties.OuterCentralizers.Coverage
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M22Table
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport

/-!
Intrinsic fixed-component exclusions for the non-J₂ sporadic rows. Actual covering centers eliminate Held components, exact orders eliminate Rudvalis, and the Mathieu rows use their marked local actions. Only the separate fixed-octad M₂₂ input remains explicit. Source: Aschbacher–Smith 2.5.19, pp.560–563.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime

/-- Held's inner covering row and outer triple-cover row have no centerless
component. The other inner centralizer has self-centralizing two-core. -/
theorem held_fixed_no_prime_component {p : ℕ} [Fact p.Prime]
    (a : MulAut Held.He) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : B ≃* PSL(2,ZMod p)) : False := by
  by_cases hi : ∃ g, a = MulAut.conj g
  · obtain ⟨g,rfl⟩ := hi
    have hg : orderOf g = 2 := (Held.InvolutionFixedData.orderOf_conj g).symm.trans ha
    rcases Held.InvolutionFixedData.Coverage.innerInvolutionCoverage g hg with
      ⟨c,rfl⟩ | ⟨c,rfl⟩
    · let e := Held.InvolutionFixedData.innerFixedEquiv (MulAut.conj c) Held.a
      have hh := (Held.InvolutionFixedData.TwoA.hasPSL3FourNormalOfIndexTwo.of_mulEquiv e).forget
      exact hh.not_component_equiv (by decide)
        (GorensteinWalter.psl2_center_eq_bot (ZMod p)) hB ⟨eB⟩
    · let e := Held.InvolutionFixedData.innerFixedEquiv (MulAut.conj c)
        (Held.TwoLocalCandidates.max5First ^ 4)
      exact Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification.held_twoB_no_component
        (B.map e.symm.toMonoidHom) (hB.map_equiv e.symm)
  · obtain ⟨n,rfl⟩ := Held.Realization.normalizer_surjective a
    have hh := Held.InvolutionFixedData.outerRow n ha (by
      rintro ⟨g,hg⟩
      exact hi ⟨g,hg.symm⟩)
    exact hh.not_component_equiv (by decide)
      (GorensteinWalter.psl2_center_eq_bot (ZMod p)) hB ⟨eB⟩

/-- The first Rudvalis involution centralizer has no prime divisor at least
seven; the second has order prime to three. This needs only their exact orders. -/
theorem rudvalis_fixed_no_prime_injective
    [IsSimpleGroup Rudvalis.Model] [Group.IsPerfect Rudvalis.Model]
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (a : MulAut Rudvalis.Model) (ha : orderOf a = 2)
    (f : PSL(2,ZMod p) →* a.fixedSubgroup) (hf : Function.Injective f) : False := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,rfl⟩ := Chapter1.XiEmbedding.OuterModels.rudvalis_conj_surjective a
  have hg : orderOf g = 2 := (orderOf_injective MulAut.conj
    (MulAut.conj_injective_of_center_eq_bot (Subgroup.center_eq_bot_of_simple_perfect)) g).symm.trans ha
  let e := MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj g)
  rcases Rudvalis.InvolutionCentralizers.centralizer_representatives g hg with h | h
  · exact prime_pslTwo_no_injective_small_fixed hp hp7
      (Or.inr (Or.inr (Or.inr (Or.inr (Rudvalis.InvolutionCentralizers.first_centralizer_card h.1)))))
      (e.toMonoidHom.comp f) (e.injective.comp hf)
  · apply pslTwo_no_injective_three_free (F := ZMod p) (D := Rudvalis.InvolutionCentralizers.Centralizer g)
      ?_ (e.toMonoidHom.comp f) (e.injective.comp hf)
    rw [Rudvalis.InvolutionCentralizers.second_class_centralizer_card h.1]
    decide

/-- Every M₂₃ involution is inner and its fixed subgroup has self-centralizing
two-core, so the actual carrier has no involution-fixed component. -/
theorem m23_fixed_no_component
    (a : MulAut _root_.Sporadic.Mathieu.M23) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) : False :=
  _root_.Sporadic.Mathieu.M23Geometry.InvolutionCentralizer.fixedSubgroup_no_component_of_inner
    a ha (_root_.Sporadic.Mathieu.m23_involution_automorphism_inner a ha) B hB


private theorem eleven_twentyThree_not_fermat_mersenne {p : ℕ} (hp : p = 11 ∨ p = 23) :
    ¬ IsFermatOrMersennePrime p := by
  intro h
  have hpow (k : ℕ) : 2 ^ k ≠ p - 1 ∧ 2 ^ k ≠ p + 1 := by
    by_cases hk : k < 5
    · interval_cases k <;> rcases hp with rfl | rfl <;> norm_num
    · have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ k by omega)
      norm_num at hh
      rcases hp with rfl | rfl <;> omega
  rcases h.2 with ⟨k,hk⟩ | ⟨k,hk⟩
  · exact (hpow (2 ^ k)).1 (by omega)
  · exact (hpow k).2 hk.symm

/-- The first M₂₄ row has no ordinary component. In the second row, its
lack of elements of order seven eliminates the only Fermat–Mersenne prime
at least seven dividing M₂₄'s order. -/
theorem m24_fixed_no_prime_component {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (a : MulAut _root_.Sporadic.Mathieu.M24) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : PSL(2,ZMod p) ≃* B) : False := by
  rcases (_root_.Sporadic.Mathieu.M24InvolutionCentralizers.fixedSubgroup_alternative a ha).2 with he | he
  · obtain ⟨e⟩ := he
    exact Chapter16.OtherPreliminaries.Mathieu.m24_twoA_no_component
      (B.map e.toMonoidHom) (hB.map_equiv e)
  · obtain ⟨e⟩ := he
    have hpc := prime_dvd_pslTwo_card hp.1 hp7
    let f := e.toMonoidHom.comp (B.subtype.comp eB.toMonoidHom)
    have hf : Function.Injective f := e.injective.comp (B.subtype_injective.comp eB.injective)
    have hd := hpc.trans (Subgroup.card_dvd_of_injective f hf)
    have hdp : p ∣ Nat.card _root_.Sporadic.Mathieu.M24 :=
      hd.trans _root_.Sporadic.Mathieu.M24InvolutionCentralizers.centralizer2B.card_subgroup_dvd_card
    rw [_root_.Sporadic.Mathieu.m24_order] at hdp
    have hfac := Nat.mem_primeFactors.mpr ⟨hp.1,hdp,by decide⟩
    have hh : Nat.primeFactors 244823040 = {2,3,5,7,11,23} := by decide +kernel
    rw [hh] at hfac
    simp only [Finset.mem_insert,Finset.mem_singleton] at hfac
    have hcases : p = 7 ∨ p = 11 ∨ p = 23 := by omega
    rcases hcases with rfl | h
    · exact _root_.Sporadic.Mathieu.M24InvolutionCentralizers.twoB_centralizer_not_seven hd
    · exact eleven_twentyThree_not_fermat_mersenne h hp


/-- The M₂₂ screen needs only the marked eight-fixed-point component
exclusion. The other outer row follows from its absence of seven-elements. -/
theorem m22_fixed_no_prime_component_of_eight
    (height : ∀ (s : _root_.Sporadic.Mathieu.m22DesignAut), orderOf s = 2 →
      s.val ∉ _root_.Sporadic.Mathieu.M22 →
      (_root_.Sporadic.Mathieu.M22OuterCentralizers.fixedPoints s).card = 8 →
      ∀ B : Subgroup (_root_.Sporadic.Mathieu.M22OuterCentralizers.centralizer s),
        ¬ IsComponent (_root_.Sporadic.Mathieu.M22OuterCentralizers.centralizer s) B)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (a : MulAut _root_.Sporadic.Mathieu.M22) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : PSL(2,ZMod p) ≃* B) : False := by
  let : Fact p.Prime := ⟨hp.1⟩
  by_cases hi : ∃ g,a = MulAut.conj g
  · obtain ⟨g,rfl⟩ := hi
    have hg : orderOf g = 2 := (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot _root_.Sporadic.Mathieu.m22_center_eq_bot) g).symm.trans ha
    exact Chapter16.OtherPreliminaries.Mathieu.m22_inner_fixedSubgroup_no_components g hg ⟨B,hB⟩
  · obtain ⟨s,hs,ho,rfl⟩ :=
      _root_.Sporadic.Mathieu.M22OuterCentralizers.exists_outer_design_involution a ha hi
    rcases _root_.Sporadic.Mathieu.M22OuterCentralizers.outer_involution_fixedPoints_card s hs ho with h8 | h0
    · exact height s hs ho h8 B hB
    · let C := _root_.Sporadic.Mathieu.M22OuterCentralizers.centralizer s
      have hd : p ∣ Nat.card C := (prime_dvd_pslTwo_card hp.1 hp7).trans
        (Subgroup.card_dvd_of_injective (B.subtype.comp eB.toMonoidHom)
          (B.subtype_injective.comp eB.injective))
      have hdp := (_root_.Sporadic.Mathieu.m22_prime_dvd_order_iff p).mp
        (hd.trans C.card_subgroup_dvd_card)
      have hcases : p = 7 ∨ p = 11 := by omega
      rcases hcases with rfl | h11
      · exact _root_.Sporadic.Mathieu.M22OuterCentralizers.fixedPointFree_centralizer_not_seven s h0 hd
      · exact eleven_twentyThree_not_fermat_mersenne (Or.inl h11) hp

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
