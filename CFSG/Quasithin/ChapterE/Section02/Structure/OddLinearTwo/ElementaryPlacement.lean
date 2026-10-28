module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeElementary
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeSeven
public import Theory.ElementaryAbelian.Join

/-!
# Inner placement of normal elementary actors in the odd prime rows

Choose an involution in the component and the center of the original Sylow.
Joining it to the original elementary normal subgroup preserves elementary
abelianness and Sylow normality. The proved source bound forces that join
to have order two, so the entire original subgroup lies in the component.
This includes the prime-seven boundary through its actual PSL₃(2) transport.
Source: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
private theorem elementary_le_normal_even_of_bound
    {H : Type*} [Group H] [Finite H] (T : Sylow 2 H)
    (K : Subgroup H) [K.Normal] (heven : 2 ∣ Nat.card K)
    (hb : ∀ W : Subgroup H, IsElementaryAbelian 2 W → W ≤ (T : Subgroup H) →
      (T : Subgroup H) ≤ normalizer (W : Set H) → Nat.card W ≤ 2)
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVT : V ≤ (T : Subgroup H))
    (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) : V ≤ K := by
  obtain ⟨t, ht, htT, hfix⟩ := normal_even_subgroup_central_sylow_involution T K heven
  let Z := zpowers (t : H)
  have ht2 : (t : H) ^ 2 = 1 := congrArg K.subtype ht.2
  let := hV
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  have hZT : Z ≤ (T : Subgroup H) := zpowers_le.mpr htT
  have hZV : Z ≤ centralizer (V : Set H) := by
    apply zpowers_le.mpr
    intro v hv
    exact mem_centralizer_singleton_iff.mp (hfix (hVT hv))
  let : IsElementaryAbelian 2 (V ⊔ Z : Subgroup H) :=
    IsElementaryAbelian.sup_of_le_centralizer hZV
  have hTZ : (T : Subgroup H) ≤ normalizer (Z : Set H) := by
    apply le_trans _ (centralizer_le_normalizer (s := (Z : Set H)))
    intro a ha z hz
    obtain ⟨n, rfl⟩ := hz
    exact (Commute.zpow_right (mem_centralizer_singleton_iff.mp (hfix ha)) n).eq.symm
  have hcard := hb (V ⊔ Z) inferInstance (sup_le hVT hZT)
    ((le_inf hVN hTZ).trans (normalizer_inf_normalizer_le_normalizer_sup V Z))
  have hZcard : Nat.card Z = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ht2 (fun he => ht.1 (Subtype.ext he))
  have heq : Z = V ⊔ Z := eq_of_le_of_card_ge le_sup_right (by omega)
  exact (le_sup_left.trans heq.ge).trans (zpowers_le.mpr t.property)

/-- Every original normal elementary Sylow subgroup acts from inside the prime-field component. -/
theorem prime_linear_source_elementary_le_component
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (eK : K ≃* PSL2MatrixGroup F)
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVT : V ≤ (T : Subgroup H)) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) :
    V ≤ K := by
  obtain ⟨S, _, t, ht, _, _, _⟩ := prime_linear_source_sylow_center T hP K hgen ho hF hp eK
  have heven : 2 ∣ Nat.card K := ht ▸ _root_.orderOf_dvd_natCard (x := t)
  exact elementary_le_normal_even_of_bound T K heven
    (prime_linear_source_elementary_card_le_two T hP K hgen hO ho hF hp eK)
    V hV hVT hVN

/-- The original prime-seven branch has the same inner placement, including cyclic V. -/
theorem prime_seven_source_elementary_le_component
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : (ChapterB.minimalParabolicMax T hP).normalCore = ⊥)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 7)
    (eK : K ≃* PSL2MatrixGroup F)
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVT : V ≤ (T : Subgroup H)) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) :
    V ≤ K := by
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨7, 1, by decide, by decide, by decide, by simpa using hF⟩
  let S : Sylow 2 K := Classical.choice inferInstance
  let S' := S.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨m, _, ⟨d⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd S'
  have hd : 2 ∣ Nat.card S' := by rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]; exact dvd_mul_right 2 _
  have heven : 2 ∣ Nat.card K := by
    rw [Nat.card_congr eK.toEquiv]
    exact hd.trans (S' : Subgroup (PSL2MatrixGroup F)).card_subgroup_dvd_card
  apply elementary_le_normal_even_of_bound T K heven _ V hV hVT hVN
  intro W hW hWT hWN
  have hlt : Nat.card W < 4 := by
    by_contra! hc
    exact prime_seven_source_not_elementary_four T hP hcore K hgen hF eK W hW hWT hWN hc
  let := hW
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
  rw [hn] at hlt ⊢
  have hn2 : n < 2 := by
    by_contra! hh
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    norm_num at this
    omega
  interval_cases n <;> norm_num
end CFSG.Quasithin.ChapterE.Structure
