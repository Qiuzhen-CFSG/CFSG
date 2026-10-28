module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.SporadicModels
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure
public import Theory.Mathieu.M23.Properties.Automorphisms
/-!
# Faithful Sylow bounds for the exceptional sections

The literal automorphism groups of J₂, M₂₃ and PSL₃(4) all have two-part
at most256. Even characteristic makes the original Sylow action faithful
when the local component has trivial two-core, giving the same bound for
the ambient Sylow. Source: Aschbacher–Smith A.3.12, pp.47–48.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
private theorem jankoTwo_aut_card_dvd :
    Nat.card (MulAut Sporadic.LeechRelated.J2.Carrier) ∣ 256 * 4725 := by
  have hi : Nat.card (MulAut.innerSubgroup Sporadic.LeechRelated.J2.Carrier) ∣ 604800 := by
    rw [← Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    exact card_dvd_of_surjective (MulAut.conj : Sporadic.LeechRelated.J2.Carrier →*
      MulAut Sporadic.LeechRelated.J2.Carrier).rangeRestrict
      (MulAut.conj : Sporadic.LeechRelated.J2.Carrier →*
        MulAut Sporadic.LeechRelated.J2.Carrier).rangeRestrict_surjective
  have ho : Nat.card (MulAut.Outer Sporadic.LeechRelated.J2.Carrier) ∣ 2 := by
    have hp := Nat.card_pos (α := MulAut.Outer Sporadic.LeechRelated.J2.Carrier)
    have hb := Sporadic.LeechRelated.J2.outer_card_le_two
    have hh : Nat.card (MulAut.Outer Sporadic.LeechRelated.J2.Carrier) = 1 ∨
      Nat.card (MulAut.Outer Sporadic.LeechRelated.J2.Carrier) = 2 := by omega
    rcases hh with hh | hh <;> simp [hh]
  rw [← (MulAut.innerSubgroup Sporadic.LeechRelated.J2.Carrier).card_mul_index]
  change Nat.card (MulAut.innerSubgroup Sporadic.LeechRelated.J2.Carrier) *
    Nat.card (MulAut.Outer Sporadic.LeechRelated.J2.Carrier) ∣ 256 * 4725
  simpa only [show 256 * 4725 = 604800 * 2 from rfl] using Nat.mul_dvd_mul hi ho


private theorem automorphism_two_part {X : Type*} [Group X] (h : IsModel X) :
    ∃ n : ℕ, Odd n ∧ Nat.card (MulAut X) ∣ 256 * n := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    refine ⟨4725, by decide, ?_⟩
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact jankoTwo_aut_card_dvd
  · obtain ⟨e⟩ := h
    refine ⟨79695, by decide, ?_⟩
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    have hd := card_dvd_of_surjective (MulAut.conj : Sporadic.Mathieu.M23 →* _)
      Sporadic.Mathieu.m23_conj_surjective
    rw [Sporadic.Mathieu.m23_order] at hd
    exact hd.trans (by decide)
  · obtain ⟨e⟩ := h
    refine ⟨945, by decide, ?_⟩
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      ← (MulAut.innerSubgroup Matrix.PSL3Four.PSL).card_mul_index]
    change Nat.card (MulAut.innerSubgroup Matrix.PSL3Four.PSL) *
      Nat.card (MulAut.Outer Matrix.PSL3Four.PSL) ∣ 256 * 945
    have hi : Nat.card (MulAut.innerSubgroup Matrix.PSL3Four.PSL) ∣ 20160 := by
      rw [← Matrix.PSL3Four.card_PSL]
      exact card_dvd_of_surjective (MulAut.conj : Matrix.PSL3Four.PSL →* _).rangeRestrict
        (MulAut.conj : Matrix.PSL3Four.PSL →* _).rangeRestrict_surjective
    simpa only [show 256 * 945 = 20160 * 12 from rfl] using
      Nat.mul_dvd_mul hi Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve

variable {G : Type*} [Group G] [Finite G]
theorem sylow_card_dvd_of_core_eq_bot (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B))
    (hc : pCore 2 B = ⊥) (hE : IsEvenCharacteristicAt S) :
    Nat.card S ∣ 256 := by
  let eB : B ≃* B ⧸ pCore 2 B :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm
  have hb : IsModel B := h.of_equiv eB
  let : IsSimpleGroup B := hb.isSimple
  let := local_perfect hB
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S hE hB hn
  let f := B.normalizerMonoidHom.comp (inclusion hn)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hf]
    refine ⟨a.property, ?_⟩
    change inclusion hn a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  obtain ⟨n,hn,hAut⟩ := automorphism_two_part hb
  have hd : Nat.card S ∣ 256 * n := (card_dvd_of_injective f hinj).trans hAut
  have hcop : Nat.Coprime (Nat.card S) n := by
    obtain ⟨m,hm⟩ := S.isPGroup'.exists_card_eq
    rw [hm]
    exact hn.coprime_two_left.pow_left m
  exact hcop.dvd_of_dvd_mul_right hd

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
