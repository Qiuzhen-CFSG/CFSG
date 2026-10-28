module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Obstruction.Primary
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs

/-!
# The intrinsic odd-extension obstruction in binary degree eight

The primary-factor theorem makes a C-component quasisimple when its central
quotient has order dividing |GL₈(2)|. With trivial two-core its center is odd,
so its odd core equals that center and the odd-core quotient is simple. An
actual SL₂(p) quotient for p>3 has a nontrivial central involution, giving the
contradiction. Thus every surviving odd extension is excluded without a
case-by-case model catalogue or inheritance through the central quotient.

Source: Aschbacher–Smith A.3.6, A.3.14(13–14), and 11.5.7,
refs/quasithin.pdf, printed pp.43–45,50,782.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.Chapter11
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Obstruction

private theorem center_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : (center A).map e.toMonoidHom = center B := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact (centerCongr e ⟨a,ha⟩).property
  · intro b hb
    exact ⟨e.symm b, (centerCongr e.symm ⟨b,hb⟩).property, e.apply_symm_apply b⟩

/-- Small central-quotient order forces an intrinsic C-component to be quasisimple. -/
theorem quasisimple_of_central_order {Q : Type*} [Group Q] [Finite Q]
    {κ : GroupClass} (hQ : IsSQTK κ Q) (hO : pCore 2 Q = ⊥)
    (hC : (⊤ : Subgroup Q).IsCComponent)
    (hd : Nat.card (Q ⧸ center Q) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))) : IsQuasisimple Q := by
  let e : ((⊤ : Subgroup Q) ⧸ center (⊤ : Subgroup Q)) ≃* (Q ⧸ center Q) :=
    QuotientGroup.congr _ _ topEquiv (center_map_equiv topEquiv)
  have hf := fitting_central_of_central_order hQ hO hC
    (by rwa [Nat.card_congr e.toEquiv])
  have hr : solvableRadical (⊤ : Subgroup Q) = center (⊤ : Subgroup Q) :=
    le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
      (le_solvableRadical _ inferInstance inferInstance)
  let := hC.perfect
  let := hC.isSimpleGroup_quotient_solvableRadical
  let : IsQuasisimple (⊤ : Subgroup Q) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
  exact IsQuasisimple.of_mulEquiv topEquiv

/-- The genuine SL₂ odd-core quotient rules out the small central-quotient order. -/
theorem not_central_order_of_SL2_odd_quotient {Q : Type*} [Group Q] [Finite Q]
    {κ : GroupClass} (hQ : IsSQTK κ Q) (hO : pCore 2 Q = ⊥)
    (hC : (⊤ : Subgroup Q).IsCComponent)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hm : Source.IsSL (Q ⧸ pPrimeCore 2 Q) 2 p) :
    ¬ Nat.card (Q ⧸ center Q) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) := by
  intro hd
  let : IsQuasisimple Q := quasisimple_of_central_order hQ hO hC hd
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : Fact p.Prime := ⟨hp⟩
  let a := ZMod.ringEquivOfPrime F hp (by simpa only [Nat.card_eq_fintype_card] using hc)
  have htwo : (2 : F) ≠ 0 := by
    intro hh
    have hz : (2 : ZMod p) = 0 := by
      simpa only [map_ofNat, map_zero] using congrArg a.symm hh
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
  have horder := Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two htwo
  have heven : 2 ∣ Nat.card Q := by
    have hv := horder ▸ orderOf_dvd_natCard (-1 : Matrix.SpecialLinearGroup (Fin 2) F)
    rw [← Nat.card_congr e.toEquiv] at hv
    exact hv.trans (card_quotient_dvd_card _)
  have heq : pPrimeCore 2 Q = center Q := by
    apply le_antisymm
    · rcases IsQuasisimple.normal_le_center_or_eq_top (pPrimeCore 2 Q) with h | h
      · exact h
      · have hh := pPrimeCore_coprime_card (p := 2) (G := Q)
        rw [h, card_top] at hh
        exact (Nat.prime_two.coprime_iff_not_dvd.mp hh heven).elim
    · apply le_sSup
      exact ⟨inferInstance, Nat.prime_two.coprime_iff_not_dvd.mpr
        (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hO _ le_rfl)⟩
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : IsSimpleGroup (Q ⧸ pPrimeCore 2 Q) :=
    (QuotientGroup.quotientMulEquivOfEq heq).isSimpleGroup
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hz : center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (center (Matrix.SpecialLinearGroup (Fin 2) F)) inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  have hn : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ∈
      center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    apply mem_center_iff.mpr
    intro g
    apply Subtype.ext
    simp
  have hone := mem_bot.mp (hz ▸ hn)
  rw [hone, orderOf_one] at horder
  norm_num at horder

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Obstruction
