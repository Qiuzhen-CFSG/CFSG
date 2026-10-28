module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsTwoLocal
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.GroupAction.ModelConjugation
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner
public import Theory.SpecificGroups.Held.SylowOrderBound
public import Theory.SpecificGroups.Held.TwoPartDivisibility
/-!
# A full Sylow cannot normalize a PSL₂(7) square in Held

The automorphisms of a simple square preserve or exchange its two factors.
Their two-part is at most 2⁹, whereas a full Held Sylow has order divisible
by 2¹⁰. Thus the actual conjugation kernel has an involution. Its Held
centralizer would contain the embedded square and have order divisible by 49,
contrary to both proved inner-involution rows. The involution is constructed
in Held itself; no involutory lift across a two-kernel is assumed.

Source application: Aschbacher--Smith, A.3.12(19) and 1.2.8, pp.48 and 506--507;
Held inner-involution centralizer orders are GLS3 Table 5.3p.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality

private theorem seven_aut_card {F : Type} [Field F] [Finite F] (hF : Nat.card F = 7) :
    Nat.card (MulAut PSL(2,F)) = 336 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hi := Theory.PSL2.prime_card_inner_index F (p := 7) (by decide) (by decide) hF
  have hc : Nat.card PSL(2,F) = 168 := by
    have hh := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ (by decide : Odd 7))
    rw [hF] at hh
    norm_num at hh
    omega
  have hinj := conj_injective_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot F)
  have hr := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hh := (MulAut.conj : PSL(2,F) →* MulAut PSL(2,F)).range.card_mul_index
  rw [←hr,hc,hi] at hh
  exact hh.symm

private theorem seven_square_aut_card_dvd {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 7) : Nat.card (MulAut (PSL(2,F) × PSL(2,F))) ∣ 336^2*2 := by
  let D := PSL(2,F)
  let : IsQuasisimple D := by
    let : IsSimpleGroup D := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF]; decide)
    let : Group.IsPerfect D := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by rw [hF]; decide)
    exact { simple := ((QuotientGroup.quotientMulEquivOfEq
      (GorensteinWalter.psl2_center_eq_bot F)).trans QuotientGroup.quotientBot).isSimpleGroup }
  let d : (MulAut D × MulAut D) →* MulAut (D × D) :=
    { toFun := fun a => a.1.prodCongr a.2
      map_one' := by ext x <;> rfl
      map_mul' := fun _ _ => rfl }
  have hd : Function.Injective d := by
    intro a b h
    apply Prod.ext
    · ext x
      exact congrArg Prod.fst (DFunLike.congr_fun h (x,1))
    · ext x
      exact congrArg Prod.snd (DFunLike.congr_fun h (1,x))
  have hi : d.range.index ∣ 2 := by
    apply d.range.index_dvd_two_iff.mpr
    refine ⟨(MulEquiv.prodComm : MulAut (D × D)), ?_⟩
    intro a
    rcases AutomorphismSquare.normal_form (GorensteinWalter.psl2_center_eq_bot F) a with
      ⟨b,c,rfl⟩ | ⟨b,c,rfl⟩
    · right
      exact ⟨(b,c),rfl⟩
    · left
      exact ⟨(b,c),by ext x <;> rfl⟩
  have hc : Nat.card d.range = 336^2 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hd).toEquiv,Nat.card_prod,
      seven_aut_card hF,pow_two]
  rw [←d.range.card_mul_index,hc]
  exact Nat.mul_dvd_mul (dvd_refl _) hi

private theorem held_involution_centralizer_not_seven_square (z : Held.He) (hz : orderOf z = 2) :
    ¬ 49 ∣ Nat.card (centralizer ({z} : Set Held.He)) := by
  rw [←MulAut.fixedSubgroup_conj]
  rcases Held.InvolutionFixedData.Coverage.innerInvolutionCoverage z hz with ⟨c,rfl⟩ | ⟨c,rfl⟩
  · rw [←Nat.card_congr (Held.InvolutionFixedData.innerFixedEquiv (MulAut.conj c) Held.a).toEquiv]
    change ¬ 49 ∣ Nat.card Held.InvolutionFixedData.TwoA.centralizer
    rw [Held.InvolutionFixedData.TwoA.FiniteStructure.centralizer_card]
    norm_num
  · rw [←Nat.card_congr (Held.InvolutionFixedData.innerFixedEquiv (MulAut.conj c)
        (Held.TwoLocalCandidates.max5First^4)).toEquiv,
      Held.InvolutionFixedData.twoB_fixedSubgroup_card]
    norm_num

/-- A full Held Sylow cannot normalize an embedded square of PSL₂(7).
The action kernel supplies an involution downstairs, with no lifting premise. -/
theorem held_no_sylow_normalized_seven_square
    (S : Sylow 2 Held.He) (W : Subgroup Held.He)
    (hSW : (S : Subgroup Held.He) ≤ normalizer (W : Set Held.He))
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 7)
    (e : W ≃* (PSL(2,F) × PSL(2,F))) : False := by
  let f := Theory.GroupAction.ModelConjugation.action (S : Subgroup Held.He) W hSW e
  have hnon : ¬ Function.Injective f := by
    intro hi
    have hd : 2^10 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card Held.two_pow_ten_dvd_card
    have hb := (card_dvd_of_injective f hi).trans (seven_square_aut_card_dvd hF)
    have hh := hd.trans hb
    norm_num at hh
  have hk : f.ker ≠ ⊥ := fun hh => hnon ((MonoidHom.ker_eq_bot_iff f).mp hh)
  have hp : IsPGroup 2 f.ker := S.isPGroup'.to_subgroup f.ker
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hnpos : 0 < n := by
    by_contra! hh
    have he : n = 0 := by omega
    have hc : Nat.card f.ker = 1 := by simpa [he] using hn
    exact hk (f.ker.eq_bot_of_card_eq hc)
  have hd : 2 ∣ Nat.card f.ker := by
    rw [hn]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2 hd
  let zS : S := z.val
  let zH : Held.He := zS.val
  have hzH : orderOf zH = 2 :=
    (orderOf_injective (S : Subgroup Held.He).subtype (S : Subgroup Held.He).subtype_injective zS).trans
      ((orderOf_injective f.ker.subtype f.ker.subtype_injective z).trans hz)
  have hc : zH ∈ centralizer (W : Set Held.He) := by
    exact ((SetLike.ext_iff.mp
      (Theory.GroupAction.ModelConjugation.action_ker (S : Subgroup Held.He) W hSW e)) zS).mp z.property
  have hW : W ≤ centralizer ({zH} : Set Held.He) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (hc w hw)
  have hcard : Nat.card W = 168^2 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    have hbase : Nat.card PSL(2,F) = 168 := by
      have hh := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ (by decide : Odd 7))
      rw [hF] at hh
      norm_num at hh
      omega
    rw [hbase,pow_two]
  apply held_involution_centralizer_not_seven_square zH hzH
  exact (show 49 ∣ Nat.card W by rw [hcard]; norm_num).trans (card_dvd_of_le hW)
end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
