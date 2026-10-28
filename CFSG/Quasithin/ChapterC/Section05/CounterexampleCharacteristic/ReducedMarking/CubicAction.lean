module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.CubicModel
public import Theory.AtlasPort.LinearGroups.SL2Order
/-!
# Surjectivity of the original reduced A₃ action

The literal K-image has order three and the original Baumann parameter
supplies a nontrivial two-element in the KT-image. The binary special linear
group has order six, so this action is onto. Its module coordinates and
centralizer kernel are those constructed from actual normalizer conjugation.

Source: Aschbacher–Smith C.5.4(2), printed p.155, the A₃ case.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

theorem cubic_reduced_action (h : Setup R K F) (hA : IsAlternatingBlock K 3)
    (T : Subgroup G) (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G)) (hST : S R ≤ T) :
    ∃ (e : U K ≃* Multiplicative (Fin 2 → ZMod 2))
      (q : (K ⊔ T : Subgroup G) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      Function.Surjective q ∧
      q.ker = (centralizer (U K : Set G)).subgroupOf (K ⊔ T) ∧
      ∀ z u, e (normalizerConjugate (inclusion (sup_le K.le_normalizer hn) z) u) =
        cubicNaturalAction (q z) (e u) := by
  obtain ⟨e,a,hker,he⟩ := cubic_normalizer_action h hA
  let A := K ⊔ T
  have hAN : A ≤ normalizer (K : Set G) := sup_le K.le_normalizer hn
  let q := a.comp (inclusion hAN)
  have hqker : q.ker = (centralizer (U K : Set G)).subgroupOf A := by
    ext z
    change inclusion hAN z ∈ a.ker ↔ _
    rw [hker]
    rfl
  let aK := q.comp (inclusion (show K ≤ A from le_sup_left))
  have hKker : aK.ker = pCore 2 K := by
    rw [← hA.2.1.centralizer_blockU]
    ext k
    change inclusion (show K ≤ A from le_sup_left) k ∈ q.ker ↔ _
    rw [hqker]
    constructor
    · intro hc u hu
      exact Subtype.ext (hc u (mem_map_of_mem K.subtype hu))
    · intro hc u hu
      obtain ⟨v,hv,rfl⟩ := hu
      exact congrArg Subtype.val (hc v hv)
  have hKcard : Nat.card aK.range = 3 := by
    rw [← index_ker,hKker,index_eq_card]
    obtain ⟨_,⟨m⟩,_⟩ := hA.2.2
    rw [Nat.card_congr m.quotientIso.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hKrange : aK.range ≤ q.range := by
    rintro _ ⟨k,rfl⟩
    exact ⟨inclusion le_sup_left k,rfl⟩
  have hthree : 3 ∣ Nat.card q.range := hKcard ▸ card_dvd_of_le hKrange
  let aS := q.comp (inclusion (show S R ≤ A from hST.trans le_sup_right))
  have hSne : aS.range ≠ ⊥ := by
    intro hz
    obtain ⟨s,hs⟩ := h.coordinates.parameter_surjective (Multiplicative.ofAdd (1 : F))
    have hc : (s : G) ∈ centralizer (U K : Set G) := by
      have hh := DFunLike.congr_fun (aS.range_eq_bot_iff.mp hz) s
      have hm : inclusion (show S R ≤ A from hST.trans le_sup_right) s ∈ q.ker := hh
      exact hqker.le hm
    have hp := (h.coordinates.parameter_kernel s).mpr hc
    rw [hs] at hp
    exact one_ne_zero (congrArg Multiplicative.toAdd hp)
  have hSp : IsPGroup 2 aS.range := (hT.to_le hST).of_surjective aS.rangeRestrict aS.rangeRestrict_surjective
  have htwo : 2 ∣ Nat.card q.range := by
    have hd : 2 ∣ Nat.card aS.range := hSp.card_eq_or_dvd.resolve_left
      (fun hh => hSne (Subgroup.card_eq_one.mp hh))
    exact hd.trans (card_dvd_of_le (show aS.range ≤ q.range from by
      rintro _ ⟨s,rfl⟩; exact ⟨inclusion (hST.trans le_sup_right) s,rfl⟩))
  have hsix : 6 ∣ Nat.card q.range := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree
  have hbound : Nat.card q.range ≤ 6 := by
    have hb := card_le_card_group q.range
    simpa only [Atlas.card_sl_two,Nat.card_zmod,Nat.reducePow,Nat.reduceSub,Nat.reduceMul] using hb
  have hcard : Nat.card q.range = 6 := le_antisymm hbound (Nat.le_of_dvd Nat.card_pos hsix)
  have hq : Function.Surjective q := MonoidHom.range_eq_top.mp (eq_top_of_card_eq q.range (by
    simpa only [Atlas.card_sl_two,Nat.card_zmod,Nat.reducePow,Nat.reduceSub,Nat.reduceMul] using hcard))
  exact ⟨e,q,hq,hqker,fun z u => he (inclusion hAN z) u⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
