module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoFirstCentralizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.SevenOrder
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order

/-!
# Four sporadic exclusions for the original binary-three point

The literal quotient B/O₂(B) has a factor seven. This excludes M₁₁ and
M₁₂ immediately, and excludes strict local containment in J₂ because
its proper full-Sylow overgroups have order prime to seven. For M₂₂,
the existing full-Sylow-normalized local PSL₃(2) exclusion applies to
the actual subgroup restricted to the containing C-component.

No quasisimplicity of B is assumed. The M₂₂ row retains the original
Sylow normalization hypothesis. The remaining six sporadic names stay
explicit; the stronger index-63 geometry of Chapter12 is not assumed.
Source: Aschbacher--Smith A.3.12 and 15.3.23, printed pp.47--48,1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem seven_dvd_binary_three_card {B : Subgroup G}
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) : 7 ∣ Nat.card B := by
  have hq : Nat.card (B ⧸ pCore 2 B) = 168 :=
    (Nat.card_congr (e.trans Matrix.PSL3Two.equiv.symm).toEquiv).trans
      Matrix.PSL3Two.card_SL
  exact (show 7 ∣ Nat.card (B ⧸ pCore 2 B) by rw [hq]; decide).trans
    (pCore 2 B).card_quotient_dvd_card

omit [Finite G] in
/-- Neither small Mathieu carrier contains the original binary-three section. -/
theorem binary_three_point_not_small_mathieu
    {B K : Subgroup G} (hBK : B ≤ K)
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) :
    ¬ (Nonempty (K ≃* Sporadic.Mathieu.M11) ∨
      Nonempty (K ≃* Sporadic.Mathieu.M12)) := by
  intro hm
  have hd := (seven_dvd_binary_three_card e).trans (card_dvd_of_le hBK)
  rcases hm with hm | hm
  all_goals obtain ⟨a⟩ := hm
  · rw [Nat.card_congr a.toEquiv,Sporadic.Mathieu.m11_order] at hd
    norm_num at hd
  · rw [Nat.card_congr a.toEquiv,Sporadic.Mathieu.m12_order] at hd
    norm_num at hd

/-- A strict local component with the original quotient cannot have J₂
as its containing C-component. -/
theorem binary_three_point_not_jankoTwo
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (a : K ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  obtain ⟨S,_,hl⟩ := exists_local_sylow_restriction T hB hBK.le hK.subnormal
  let A := B.subgroupOf K
  let J := A ⊔ (S : Subgroup K)
  have hJ : J ≠ ⊤ := by
    intro ht
    have hc : A.IsCComponent := by
      change (A.subgroupOf J).IsCComponent at hl
      rw [ht] at hl
      simpa only [map_subgroupOf_eq_of_le le_top] using hl.map_subtype (.top)
    exact hBK.ne (le_antisymm hBK.le
      (subgroupOf_eq_top.mp (hK.eq_top_of_isCComponent hc)))
  let b := subgroupOfEquivOfLe hBK.le
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have h7 : 7 ∣ Nat.card J := (seven_dvd_binary_three_card (bq.trans e)).trans
    (card_dvd_of_le (show A ≤ J from le_sup_left))
  apply Sporadic.LeechRelated.J2.SylowOvergroups.proper_overgroup_not_seven_dvd
    (S.mapSurjective (f := a.toMonoidHom) a.surjective) (J.map a.toMonoidHom)
    (map_mono (show (S : Subgroup K) ≤ J from le_sup_right)) ?_
  · rwa [card_map_of_injective a.injective]
  · intro ht
    apply hJ
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]

/-- The actual M₂₂ carrier is impossible when the original full Sylow
normalizes B. The existing M₂₂ theorem does not assume B quasisimple. -/
theorem binary_three_point_not_mathieuTwentyTwo
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (a : K ≃* Sporadic.Mathieu.M22) : False := by
  obtain ⟨S,_,hl,hn⟩ := exists_local_sylow_normalizing T hB hK.subnormal hBK hTB
  let b := subgroupOfEquivOfLe hBK
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  exact JankoMathieu.not_three_of_m22_surjection a.toMonoidHom a.surjective
    S (B.subgroupOf K) hl hn
    ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨bq.trans e⟩⟩

/-- The unchanged actual sporadic carrier is one of these six names.
All their original equivalences remain available to the caller. -/
theorem binary_three_point_sporadic_model_remaining
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (name : ClassificationModels.SporadicName) (hj : name ≠ .j3)
    (hm : Nonempty (K ≃* name.Carrier)) :
    name = .m23 ∨ name = .m24 ∨ name = .j4 ∨ name = .hs ∨ name = .he ∨ name = .ru := by
  cases name with
  | m11 => exact (binary_three_point_not_small_mathieu hBK.le e (.inl hm)).elim
  | m12 => exact (binary_three_point_not_small_mathieu hBK.le e (.inr hm)).elim
  | m22 => exact (binary_three_point_not_mathieuTwentyTwo T hB hK hBK.le hTB e hm.some).elim
  | m23 => exact .inl rfl
  | m24 => exact .inr (.inl rfl)
  | j2 => exact (binary_three_point_not_jankoTwo T hB hK hBK e hm.some).elim
  | j3 => exact (hj rfl).elim
  | j4 => exact .inr (.inr (.inl rfl))
  | hs => exact .inr (.inr (.inr (.inl rfl)))
  | he => exact .inr (.inr (.inr (.inr (.inl rfl))))
  | ru => exact .inr (.inr (.inr (.inr (.inr rfl))))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
