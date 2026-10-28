module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.RankOneExclusion
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# Recognizing the original quotient inside the seven-letter actor

The actual smaller image in A₇ retains the original two-core quotient.
The nonnormal-component catalogue and its order divisor 2520 exclude
Suzuki and J₁. A binary rank-one section forces field order four and the
forbidden A₅ quotient. In odd prime characteristic only five and seven
survive divisibility; five is A₅ and seven is SL₃(2).

Combining this with the torus exclusion recognizes SL₃(2) whenever the
original moved subgroup lies in the prepared reduced orbit. No original
representation is inferred from that group isomorphism. QuietRecognition
applies the result to the original irreducible covers.
Source: Aschbacher--Smith 1.2.1(3) and10.2.9, printed pp.504,751--752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterB.QuasisimpleSource Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

private theorem prime_psl_small
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q] [Nontrivial Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL Q 2 p)
    (hd : Nat.card Q ∣ 2520)
    (hna : ¬ Nonempty (Q ≃* alternatingGroup (Fin 5))) :
    Nonempty (Q ≃* SL(3,ZMod 2)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : Fact p.Prime := ⟨hp⟩
  let a : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let f := e.trans (Atlas.fieldEquivPSL 2 a)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩
  have hc : Nat.card Q = p * (p^2-1) / 2 := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F hodd,hF]
  have hmul : Nat.card Q * 2 = p * (p^2-1) := by
    rw [hc]
    apply Nat.div_mul_cancel
    have he : Even (p^2-1) := by
      obtain ⟨k,hk⟩ := ho.pow (n := 2)
      refine ⟨k,?_⟩
      omega
    exact dvd_mul_of_dvd_right he.two_dvd p
  have hpd : p ∣ 5040 := by
    have hh : p ∣ Nat.card Q * 2 := hmul.symm ▸ dvd_mul_right p (p^2-1)
    exact hh.trans (Nat.mul_dvd_mul_right hd 2)
  have hgt : 3 < p := by
    rw [←hF]
    apply Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hF.symm ▸ ho)
    intro hs
    let : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.IsPerfect.not_isSolvable Q inferInstance
  have hp57 : p = 5 ∨ p = 7 := by
    have hh : p ∣ 2^4 * 3^2 * 5 * 7 := by norm_num; exact hpd
    rcases hp.dvd_mul.mp hh with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
          omega
        · have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
          omega
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h)
  rcases hp57 with rfl | rfl
  · exact (hna ⟨f.trans Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some⟩).elim
  · exact ⟨f.trans Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two⟩

/-- The original non-A5 quotient in the literal seven-letter actor is binary-three. -/
theorem Context.binary_three_quotient_of_seven_actor (c : Context D t v I)
    (a : ActionFacts c) : letI := c.reduced.normal
    ∀ (_E : ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
      alternatingGroup (Fin 7)), Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) := by
  let := c.reduced.normal
  intro E
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  let B := ((L.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))).subgroupOf A
  obtain ⟨b⟩ := c.small_local_quotient a
  have hd : Nat.card (L ⧸ pCore 2 L) ∣ 2520 := by
    rw [←Nat.card_congr b.toEquiv]
    have hh := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
    rw [Nat.card_congr E.toEquiv,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh ⊢
    exact hh
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem)
  let := D.quasisimple
  let := Selection.ModuleChoice.component_quotient_simple D hn
  cases Selection.ModuleChoice.component_quotient_model D hn with
  | linear_even n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact (c.no_seven_actor_of_rankOne_quotient a (by omega) hF
      (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm) E).elim
  | linear_prime p hp ho hm => exact prime_psl_small hp ho hm hd c.nonA5
  | janko hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  | suzuki m hm he =>
    rw [Nat.card_congr he.some.toEquiv,
      BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega)] at hd
    have h64 : 64 ∣ (2^(2*m+1))^2 := by
      rw [←pow_mul]
      exact pow_dvd_pow 2 (by omega : 6 ≤ (2*m+1)*2)
    have h := h64.trans ((dvd_mul_left _ _).trans ((dvd_mul_right _ _).trans hd))
    norm_num at h

/-- Full original moved-span inclusion forces the exact binary-three quotient. -/
theorem Context.binary_three_quotient_of_moved_le (c : Context D t v I)
    (a : ActionFacts c) (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) := by
  rcases c.seven_actor_or_binaryThree_of_moved_le a hspan with hs | hb
  · exact c.binary_three_quotient_of_seven_actor a hs.some
  · exact hb

end CFSG.Quasithin.Chapter10.PointControl.Constrained
