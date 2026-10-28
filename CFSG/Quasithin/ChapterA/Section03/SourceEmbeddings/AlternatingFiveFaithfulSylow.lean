module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import Theory.Alternating.Aut

/-!
# The Sylow order obstruction for a local A₅

The normalizing Sylow subgroup acts faithfully on a quasisimple local A₅
in an ambient group of even characteristic. Its image lies in Aut(A₅)=S₅,
so its order divides eight. Thus the ambient group order is not divisible
by sixteen. This excludes the large even-characteristic containing rows
in the contained-layer branch of Aschbacher--Smith 10.2.1.

Source: A.3.14, printed pp.49--50, and 10.2.1, printed p.743.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
variable {G : Type*} [Group G] [Finite G]

/-- Faithful conjugation on the actual A₅ bounds the full Sylow order by eight. -/
theorem sylow_card_dvd_of_faithful (S : Sylow 2 G) (B : Subgroup G)
    (e : B ≃* alternatingGroup (Fin 5))
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) : Nat.card S ∣ 8 := by
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
  let eA : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  let j := eA.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp f)
  have hj : Function.Injective j := eA.symm.injective.comp ((MulAut.congr e).injective.comp hf)
  have hd : Nat.card S ∣ 8 * 15 := by
    have hd := card_dvd_of_injective j hj
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,
      show Nat.factorial 5 = 8 * 15 from rfl] using hd
  have hcop : Nat.Coprime (Nat.card S) 15 := by
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 15).pow_left n
  exact hcop.dvd_of_dvd_mul_right hd

/-- Even characteristic supplies faithfulness for the original local A₅. -/
theorem sylow_card_dvd_of_evenCharacteristic
    (S : Sylow 2 G) (hE : IsEvenCharacteristicAt S)
    {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (e : B ≃* alternatingGroup (Fin 5)) : Nat.card S ∣ 8 := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup B := e.isSimpleGroup
  let eB : B.subgroupOf (B ⊔ (S : Subgroup G)) ≃* B := subgroupOfEquivOfLe le_sup_left
  let := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := eB.toMonoidHom) eB.surjective
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  exact sylow_card_dvd_of_faithful S B e hSB
    (sylow_centralizer_eq_bot_of_evenCharacteristic S hE hB hSB)

/-- A full-Sylow local A₅ is incompatible with a factor sixteen in an
even-characteristic ambient group. -/
theorem not_sixteen_dvd_of_evenCharacteristic
    (S : Sylow 2 G) (hE : IsEvenCharacteristicAt S)
    {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (e : B ≃* alternatingGroup (Fin 5)) : ¬ 16 ∣ Nat.card G := by
  intro hd
  have hs : 16 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 4) hd
  have hh := hs.trans (sylow_card_dvd_of_evenCharacteristic S hE hB hSB e)
  norm_num at hh

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
