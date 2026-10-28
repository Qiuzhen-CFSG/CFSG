module
public import CFSG.Quasithin.Chapter1.Section01Overgroups
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Stellmacher.OmegaOneCenterMap

/-!
# The central witness and characteristic-two inheritance in C.5.10

A nontrivial elementary normal subgroup of the full Sylow group supplies
an involution in its center. If it lies in V, then 1.1.4(3) puts N_G(V)
in He. An intermediate subgroup containing half of the original Sylow
inherits characteristic two by the cardinal bound in 1.1.4(7).

Source: Aschbacher–Smith, C.5.10, printed p.161.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
variable {G : Type*} [Group G] [Finite G]

theorem central_witness (T E V : Subgroup G) (hT : IsPGroup 2 T)
    (hET : E ≤ T) (hEn : T ≤ normalizer (E : Set G)) (hE : E ≠ ⊥)
    (hElem : IsElementaryAbelian 2 E) (hEV : E ≤ V) :
    V ⊓ omegaOneCenterAmbient T ≠ ⊥ := by
  let E' := E.subgroupOf T
  let : E'.Normal := (normal_subgroupOf_iff_le_normalizer hET).mpr hEn
  have hE' : E' ≠ ⊥ := by
    intro he
    apply hE
    rw [← map_subgroupOf_eq_of_le hET,show E.subgroupOf T = ⊥ from he,Subgroup.map_bot]
  have hc := center_inf_ne_bot_of_normal hT E' hE'
  obtain ⟨⟨z,hz⟩,hz1⟩ := ne_bot_iff_exists_ne_one.mp hc
  intro he
  have hm : (z : G) ∈ V ⊓ omegaOneCenterAmbient T := by
    refine ⟨hEV hz.2,(mem_omegaOneCenterAmbient_iff T _).mpr ⟨z.property,?_,?_⟩⟩
    · let := hElem
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hz.2
    · intro t ht
      exact congrArg T.subtype (mem_center_iff.mp hz.1 (⟨t,ht⟩ : T))
  have hzG : (z : G) = 1 := by simpa only [he,mem_bot] using hm
  exact hz1 (Subtype.ext (Subtype.ext hzG))

theorem half_sylow_inheritance (T : Sylow 2 G) (T₁ M X : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (hT₁X : T₁ ≤ X) (hXM : X ≤ M) (hX : X ≠ ⊥) (hM : M ∈ Chapter1.He G) :
    X ∈ Chapter1.He G := by
  have hT₁M := hT₁X.trans hXM
  obtain ⟨P,hP⟩ := ((T.isPGroup'.to_le hT₁T).comap_subtype (K := M)).exists_le_sylow
  let B := (P : Subgroup M).map M.subtype
  have hT₁B : T₁ ≤ B := by
    rw [← map_subgroupOf_eq_of_le hT₁M]
    exact map_mono hP
  obtain ⟨Z,hBZ⟩ := (P.isPGroup'.map M.subtype).exists_le_sylow
  have hcard : Nat.card B ≤ Nat.card T :=
    (Nat.card_le_card_of_injective (inclusion hBZ) (inclusion_injective hBZ)).trans_eq (Nat.card_congr (Z.equiv T).toEquiv)
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup G) T₁ B bot_le hT₁B
  have hmulT := relIndex_mul_relIndex (⊥ : Subgroup G) T₁ (T : Subgroup G) bot_le hT₁T
  simp only [relIndex_bot_left,hhalf] at hmul hmulT
  have hi : T₁.relIndex B ≤ 2 := by
    have hp : 0 < Nat.card T₁ := Nat.card_pos
    nlinarith
  apply Chapter1.lemma_1_1_4_7 hM P hX hXM
  have he := relIndex_map_map_of_injective (X.subgroupOf M) (P : Subgroup M) M.subtype_injective
  rw [map_subgroupOf_eq_of_le hXM] at he
  rw [← he]
  have hne : T₁.relIndex B ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hmul
    exact (Nat.card_pos (α := B)).ne' hmul.symm
  exact (relIndex_le_of_le_left hT₁X hne).trans hi

theorem mem_He_of_central_witness (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (T₁ V X : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (hVT₁ : V ≤ T₁) (hT₁X : T₁ ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hw : V ⊓ omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥) : X ∈ Chapter1.He G := by
  have hV : V ≠ ⊥ := by intro he; apply hw; simp [he]
  have hc : (center (T : Subgroup G)).map (T : Subgroup G).subtype ⊓ V ≠ ⊥ := by
    intro he
    apply hw
    apply bot_unique
    intro z hz
    have hm := (mem_omegaOneCenterAmbient_iff _ _).mp hz.2
    have hh : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype ⊓ V := by
      refine ⟨⟨⟨z,hm.1⟩,mem_center_iff.mpr ?_,rfl⟩,hz.1⟩
      intro t
      exact Subtype.ext (hm.2.2 t t.property)
    simpa only [he] using hh
  have hNv := (Chapter1.lemma_1_1_4_3 T hE hV (T.isPGroup'.to_le (hVT₁.trans hT₁T)) hc).2.2
  exact half_sylow_inheritance T T₁ _ X hT₁T hhalf hT₁X hXV
    (fun he => hV (bot_unique (he ▸ hVT₁.trans hT₁X))) hNv
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
