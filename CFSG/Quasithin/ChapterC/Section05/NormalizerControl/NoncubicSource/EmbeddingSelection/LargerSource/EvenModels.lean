module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.TwistedRankTwo
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Sporadic
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverSeparation
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.Triality
public import CFSG.Quasithin.MainConverse.ReeLocal
public import CFSG.Quasithin.MainConverse.MathieuLocal
public import CFSG.Quasithin.MainConverse.SporadicLocal
/-!
# Restricted larger-component rows in even characteristic

The actual containing carrier has even characteristic by its proved local
geometry. Consequently its intrinsic full Sylow acts faithfully on the
quasisimple smaller local component. The binary rank/order bounds exclude
triality, Ree and every sporadic model. The same argument passes through
the odd center of the Mathieu triple cover. A smaller SL2(5) is impossible
because its central involution belongs to the Sylow action kernel.

These statements use local membership and normalization, with no assumed
faithfulness of the original larger-quotient Sylow.
Source: Aschbacher–Smith A.3.12 and C.5.12–13, pp.47–48,162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

theorem sporadic_evenCharacteristic (name : ClassificationModels.SporadicName)
    (e : G ≃* name.Carrier) : IsEvenCharacteristic G := by
  cases name with
  | m11 => exact MainConverse.m11_evenCharacteristic_of_iso e
  | m12 => exact MainConverse.m12_evenCharacteristic_of_iso e
  | m22 => exact MainConverse.m22_evenCharacteristic_of_iso e
  | m23 => exact MainConverse.m23_evenCharacteristic_of_iso e
  | m24 => exact MainConverse.m24_evenCharacteristic_of_iso e
  | j2 => exact (MainConverse.SporadicLocal.j2_qt_e_of_equiv e).2
  | j3 => exact (MainConverse.SporadicLocal.j3_qt_e_of_equiv e).2
  | j4 => exact (MainConverse.SporadicLocal.j4_qt_e_of_equiv e).2
  | hs => exact (MainConverse.SporadicLocal.hs_qt_e_of_equiv e).2
  | he => exact (MainConverse.SporadicLocal.he_qt_e_of_catalogue_equiv e).2
  | ru => exact (MainConverse.SporadicLocal.ru_qt_e_of_equiv e).2

omit [Finite G] in
/-- Even characteristic forbids the smaller central two-cover. -/
theorem not_sl2_five_of_faithful_sylow (T : Sylow 2 G) (B : Subgroup G)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥)
    (hB : IsSL B 2 5) : False := by
  have hc := sl2_five_center_card hB
  have hz := center_eq_bot_of_twoGroup_of_faithful_sylow T hTB hfaith
    (IsPGroup.of_card (n := 1) (by simpa using hc))
  rw [hz,card_bot] at hc
  omega

theorem not_sl2_five_local_of_evenCharacteristic (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) : ¬ IsSL B 2 5 := by
  exact not_sl2_five_of_faithful_sylow T B hTB
    (sylow_centralizer_eq_bot_of_evenCharacteristic T hE hB hTB)

theorem not_binary_local_triality (T : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (hmodel : ClassicalGroup.IsPSL B 2 (2^n)) :
    ¬ Triality.Standard.IsTrialityGroupAt (2^m) G := by
  intro he
  have hE := (MainConverse.TrialityLocal.quasithin_and_evenCharacteristic_of_isTrialityGroupAt m hm he).2
  exact not_triality_containing T B ⊤ hn (by omega) hmodel le_top hTB
    (sylow_centralizer_eq_bot_of_evenCharacteristic T (hE T) hB hTB)
    (he.of_mulEquiv (topEquiv (G := G)))

theorem not_binary_local_ree (T : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (hmodel : ClassicalGroup.IsPSL B 2 (2^n)) : ¬ IsReeF4At G m := by
  rintro ⟨d,⟨e⟩⟩
  have hE := (MainConverse.ReeLocal.quasithin_evenCharacteristic_of_iso hm (e.trans d.modelEquiv)).2
  exact not_ree_containing T B ⊤ hn hm hmodel le_top hTB
    (sylow_centralizer_eq_bot_of_evenCharacteristic T (hE T) hB hTB)
    ⟨d,⟨(topEquiv (G := G)).trans e⟩⟩

theorem not_binary_local_sporadic (T : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n) (hmodel : ClassicalGroup.IsPSL B 2 (2^n))
    (name : ClassificationModels.SporadicName) (hne : name ≠ .j3) :
    ¬ Nonempty (G ≃* name.Carrier) := by
  rintro ⟨e⟩
  have hE := sporadic_evenCharacteristic name e
  exact not_sporadic_containing T B ⊤ le_top hn hmodel hTB
    (sylow_centralizer_eq_bot_of_evenCharacteristic T (hE T) hB hTB)
    name hne ⟨(topEquiv (G := G)).trans e⟩

/-- The original intrinsic Sylow stays faithful through the genuine odd center. -/
theorem sylow_faithful_of_m22_cover (T : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hmodel : IsM22Cover G) :
    (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥ := by
  obtain ⟨_,⟨ec⟩,⟨eq⟩⟩ := hmodel
  let q := QuotientGroup.mk' (center G)
  have hk : q.ker = center G := QuotientGroup.ker_mk' _
  let : Group.IsSolvable (center G) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  let : Group.IsSolvable q.ker := hk.symm ▸ (inferInstance : Group.IsSolvable (center G))
  apply sylow_centralizer_eq_bot_of_odd_quotient_evenCharacteristic T q
    (QuotientGroup.mk'_surjective _) ?_ (MainConverse.m22_evenCharacteristic_of_iso eq) hB hTB
  rw [hk,Nat.card_congr ec.toEquiv]
  norm_num

theorem not_binary_local_m22_cover (T : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n) (hmodel : ClassicalGroup.IsPSL B 2 (2^n)) :
    ¬ IsM22Cover G := by
  intro hG
  have hfaith := sylow_faithful_of_m22_cover T hB hTB hG
  have htop : IsM22Cover (⊤ : Subgroup G) := by
    obtain ⟨hq,⟨ec⟩,⟨eq⟩⟩ := hG
    let e := topEquiv (G := G)
    let : IsQuasisimple G := hq
    refine ⟨IsQuasisimple.of_mulEquiv e.symm,⟨(centerCongr e).trans ec⟩,?_⟩
    exact ⟨(QuotientGroup.congr _ _ e (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro x hx
        exact ⟨e.symm x,(centerCongr e).symm ⟨x,hx⟩ |>.property,e.apply_symm_apply x⟩)).trans eq⟩
  exact not_mathieu_twentyTwo_cover_containing T B ⊤ le_top hn hmodel hTB hfaith htop

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
