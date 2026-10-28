module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.EvenRankTwoBasic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import Theory.Alternating.Aut

/-!
# The faithful Sylow action on an ordinary local A₈

When the intrinsic two-core vanishes, the original local group is A₈.
Even characteristic makes its full-Sylow conjugation action faithful.
The actual Aut(A₈) = S₈ comparison then forces the Sylow order to divide 128.
Source: Aschbacher–Smith A.3.12 and 15.3.32(3), pp.47–48 and 1132.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G]

theorem sylow_card_dvd_of_faithful (S : Sylow 2 G) (B : Subgroup G)
    (e : B ≃* alternatingGroup (Fin 8))
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) : Nat.card S ∣ 128 := by
  let f := B.normalizerMonoidHom.comp (inclusion hSB)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hfaith]
    refine ⟨a.property, ?_⟩
    change inclusion hSB a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  let eA : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))
  let j := eA.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp f)
  have hj : Function.Injective j := eA.symm.injective.comp ((MulAut.congr e).injective.comp hf)
  have hd : Nat.card S ∣ 128 * 315 := by
    have hd := card_dvd_of_injective j hj
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,
      show Nat.factorial 8 = 128 * 315 from rfl] using hd
  have hcop : Nat.Coprime (Nat.card S) 315 := by
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 315).pow_left n
  exact hcop.dvd_of_dvd_mul_right hd

theorem sylow_card_dvd_of_core_eq_bot
    (S : Sylow 2 G) (hE : IsEvenCharacteristicAt S)
    {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hA : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B = ⊥) :
    Nat.card S ∣ 128 := by
  obtain ⟨e⟩ := quotient_equiv hA
  let eB : B ≃* alternatingGroup (Fin 8) :=
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).symm.trans e
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup B := eB.isSimpleGroup
  let := local_perfect hB
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S hE hB hSB
  exact sylow_card_dvd_of_faithful S B eB hSB hf

theorem not_twoPower_dvd_of_core_eq_bot
    (S : Sylow 2 G) (hE : IsEvenCharacteristicAt S)
    {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hA : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B = ⊥) :
    ¬ 256 ∣ Nat.card G := by
  intro hd
  have hs : 256 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 8) hd
  have hc := hs.trans (sylow_card_dvd_of_core_eq_bot S hE hB hSB hA hcore)
  norm_num at hc

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
