module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Normalizer bounds for alternating-six sections

Suppose A/O₂(A) is A₆ and A normalizes no nontrivial two-subgroup of the
ambient group. Apply this to O₂(A) and to the intersection of a two-subgroup
with C(A). Thus A is A₆ and its normalizer acts faithfully on A inside each
two-subgroup. The actual Aut(A₆) Sylow order gives an intersection bound of
32. Normalizer index at most four consequently bounds the two-subgroup's
order by128.

The Sp₄ and G₂ consumers discharge the no-two-subgroup premise by their
parabolic geometry. This supplies the index-four model comparison in
Aschbacher--Smith 12.6.17, printed p.827 (combined 1 March2004 manuscript).
-/

public noncomputable section
namespace Theory.SpecificGroups.Alternating
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- If an A₆ section normalizes no nontrivial two-subgroup, its normalizer
meets every two-subgroup in order at most 32, the Sylow order of Aut(A₆). -/
theorem six_section_sylow_normalizer_bound
    (A : Subgroup G) (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (hA : ∀ R : Subgroup G, IsPGroup 2 R → A ≤ normalizer (R : Set G) → R = ⊥)
    (S : Subgroup G) (hS : IsPGroup 2 S) :
    Nat.card (normalizer (A : Set G) ⊓ S : Subgroup G) ≤ 32 := by
  have hcore : A.pCoreIn 2 = ⊥ := hA _ (isPGroup_pCoreIn 2 A)
    (A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hcore' : pCore 2 A = ⊥ := by
    apply map_injective A.subtype_injective
    simpa only [Subgroup.pCoreIn,Subgroup.map_bot] using hcore
  let a : A ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcore'.symm)).trans e
  let P := normalizer (A : Set G) ⊓ S
  have hP : IsPGroup 2 P := hS.to_le inf_le_right
  have hC : centralizer (A : Set G) ⊓ S = ⊥ := by
    apply hA _ (hS.to_le inf_le_right)
    exact (le_centralizer_iff.mp inf_le_left).trans (Subgroup.centralizer_le_normalizer _)
  let f := (MulAut.congr a).toMonoidHom.comp
    (A.normalizerMonoidHom.comp (inclusion (show P ≤ normalizer (A : Set G) from inf_le_left)))
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hx0 : A.normalizerMonoidHom (inclusion (show P ≤ normalizer (A : Set G) from inf_le_left) x) = 1 :=
      (MulAut.congr a).injective (hx.trans (map_one _).symm)
    have hxc : (x : G) ∈ centralizer (A : Set G) := by
      have hh : inclusion (show P ≤ normalizer (A : Set G) from inf_le_left) x ∈
          A.normalizerMonoidHom.ker := hx0
      rwa [normalizerMonoidHom_ker] at hh
    exact Subtype.ext (mem_bot.mp (hC ▸ (show (x : G) ∈ centralizer (A : Set G) ⊓ S from
      ⟨hxc,x.property.2⟩)))
  obtain ⟨Q,hQ⟩ := (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hcard : Nat.card P ≤ Nat.card Q := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact card_le_of_le hQ
  exact hcard.trans_eq (AlternatingSix.ShadowLocal.sylow_card Q)

omit [Finite G] in
/-- An index-at-most-four normalizer would force the Sylow order to be at most 128. -/
theorem six_section_sylow_card_le
    (A : Subgroup G) (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (hA : ∀ R : Subgroup G, IsPGroup 2 R → A ≤ normalizer (R : Set G) → R = ⊥)
    (S : Subgroup G) (hS : IsPGroup 2 S)
    (hi : (normalizer (A : Set G)).relIndex S ≤ 4) : Nat.card S ≤ 128 := by
  have hb := six_section_sylow_normalizer_bound A e hA S hS
  have hh := ((normalizer (A : Set G)).subgroupOf S).card_mul_index
  have hc := Nat.card_congr
    (subgroupOfEquivOfLe (show normalizer (A : Set G) ⊓ S ≤ S from inf_le_right)).toEquiv
  have he : (normalizer (A : Set G)).subgroupOf S =
      (normalizer (A : Set G) ⊓ S).subgroupOf S := by ext x; simp
  change Nat.card ((normalizer (A : Set G)).subgroupOf S) *
    (normalizer (A : Set G)).relIndex S = Nat.card S at hh
  rw [show Nat.card ((normalizer (A : Set G)).subgroupOf S) =
    Nat.card (normalizer (A : Set G) ⊓ S : Subgroup G) from (congrArg (fun P : Subgroup S => Nat.card P) he).trans hc] at hh
  change Nat.card (normalizer (A : Set G) ⊓ S : Subgroup G) *
    (normalizer (A : Set G)).relIndex S = Nat.card S at hh
  nlinarith
end Theory.SpecificGroups.Alternating
