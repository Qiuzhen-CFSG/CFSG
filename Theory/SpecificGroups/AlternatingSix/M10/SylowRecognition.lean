module

public import Theory.SpecificGroups.AlternatingSix.M10.SylowRecognition.Coordinates
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification
public import Theory.SpecificGroups.AlternatingSix.M10.Action.Extension
public import Theory.SpecificGroups.AlternatingSix.M10.SylowRecognition.Faithfulness

/-!
# The marked recognition of M₁₀ by its semidihedral Sylow subgroup

The faithful conjugation action embeds the group in the actual Aut(A₆).
The marked inner reflection in a containing Sylow holomorph selects the
specific M₁₀ extension. The final equivalence retains the image of A₆.

Source: Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446).
-/

public section
open Subgroup
namespace AlternatingSix.M10.SylowRecognition
open ShadowLocal

private theorem selected_mem_extension (P : Sylow 2 AutA6)
    (x : Holomorph.Model) (hx : x ∈ Coordinates.selected) :
    (Identification.sylowEquiv P x : AutA6) ∈ extension := by
  rw [Identification.sylowEquiv_coe]
  apply (inferInstance : extension.Normal).conj_mem
  obtain ⟨i, j, k, rfl⟩ := Coordinates.selected_normal_form x hx
  simp only [map_mul, map_pow, Identification.embedding_rotation,
    Identification.embedding_reflection, Identification.embedding_transposition]
  have hr : Identification.rotation ^ 2 ∈ extension := by
    rw [Identification.rotation_sq]
    exact Action.inner_le_extension ⟨dihedralRotation, (permutationAction_coe _).symm⟩
  have hc : Identification.reflection ∈ extension :=
    Action.inner_le_extension ⟨dihedralReflection, (permutationAction_coe _).symm⟩
  have ht : Identification.rotation * Identification.transposition ∈ extension :=
    (show zpowers (Identification.rotation * Identification.transposition) ≤ extension
      from le_sup_right) (mem_zpowers _)
  exact extension.mul_mem (extension.mul_mem (extension.pow_mem hr _) (extension.pow_mem hc _))
    (extension.pow_mem ht _)

private theorem range_le_selected {G : Type*} [Group G]
    (t : G →* Holomorph.Model) (ht : Function.Injective t)
    (a b : G) (ha : orderOf a = 8) (hb : b ^ 2 = 1)
    (hab : b * a * b⁻¹ = a ^ 3) (hg : closure ({a, b} : Set G) = ⊤)
    (href : Holomorph.reflection ∈ t.range) : t.range ≤ Coordinates.selected := by
  have hfour : (t a) ^ 4 ≠ 1 := by
    intro he
    have he' : a ^ 4 = 1 := ht (by simpa only [map_pow, map_one] using he)
    have hd := orderOf_dvd_of_pow_eq_one he'
    rw [ha] at hd
    norm_num at hd
  have hb' : (t b) ^ 2 = 1 := by rw [← map_pow, hb, map_one]
  have hab' : t b * t a * (t b)⁻¹ = (t a) ^ 3 := by
    simpa only [map_mul, map_inv, map_pow] using congrArg t hab
  have href' : ∃ (i : Fin 8) (j : Fin 2),
      Holomorph.reflection = (t a) ^ i.val * (t b) ^ j.val := by
    obtain ⟨u, hu⟩ := href
    obtain ⟨i, hi, he | he⟩ := Semidihedral.normal_form a b 8 3 (by decide) ha hb hab hg u
    · refine ⟨⟨i, hi⟩, 0, ?_⟩
      simpa only [Fin.val_zero, pow_zero, mul_one, map_pow, he] using hu.symm
    · refine ⟨⟨i, hi⟩, 1, ?_⟩
      simpa only [Fin.val_one, pow_one, map_pow, map_mul, he] using hu.symm
  obtain ⟨hat, hbt⟩ := Coordinates.generators_selected (t a) (t b) hfour hb' hab' href'
  rintro _ ⟨u, rfl⟩
  obtain ⟨i, _, rfl | rfl⟩ := Semidihedral.normal_form a b 8 3 (by decide) ha hb hab hg u
  · rw [map_pow]
    exact Coordinates.selected.pow_mem hat _
  · rw [map_mul, map_pow]
    exact Coordinates.selected.mul_mem (Coordinates.selected.pow_mem hat _) hbt

private theorem index_two_sylow_intersection {W : Type*} [Group W] [Finite W]
    (f : W →* AutA6) (hcard : Nat.card f.range = 720)
    (S : Sylow 2 W) (hf : Function.Injective f)
    (hS : Nat.card S = 16) (P : Sylow 2 AutA6)
    (hSP : (S : Subgroup W).map f ≤ (P : Subgroup AutA6)) :
    ((S : Subgroup W).map f).subgroupOf P = f.range.subgroupOf P := by
  have hi : f.range.index = 2 := by
    have hc := f.range.card_mul_index
    rw [hcard, card_aut] at hc
    omega
  let : f.range.Normal := normal_of_index_eq_two hi
  have hd : (f.range.subgroupOf P).index ∣ 2 := by
    simpa only [relIndex, hi] using f.range.relIndex_dvd_index_of_normal (P : Subgroup AutA6)
  have hiP : (f.range.subgroupOf P).index = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he | he
    · have hle : (P : Subgroup AutA6) ≤ f.range := relIndex_eq_one.mp he
      have hc := card_dvd_of_le hle
      rw [sylow_card, hcard] at hc
      norm_num at hc
    · exact he
  have hcP : Nat.card (f.range.subgroupOf P) = 16 := by
    have hc := (f.range.subgroupOf P).card_mul_index
    rw [hiP, sylow_card] at hc
    omega
  apply eq_of_le_of_card_ge
  · intro x hx
    exact map_le_range f S hx
  · rw [Nat.card_congr (subgroupOfEquivOfLe hSP).toEquiv,
      card_map_of_injective hf, hS, hcP]

private theorem sylow_image_le_extension {W : Type*} [Group W] [Finite W]
    (f : W →* AutA6) (hf : Function.Injective f)
    (hinner : ShadowLocal.inner ≤ f.range) (hcard : Nat.card f.range = 720)
    (S : Sylow 2 W) (s : S ≃* Semidihedral.StandardModel 4 (by decide)) :
    (S : Subgroup W).map f ≤ extension := by
  have hS : Nat.card S = 16 := (Nat.card_congr s.toEquiv).trans
    (Semidihedral.standardModel_card 4 (by decide))
  obtain ⟨P, hSP⟩ := (S.isPGroup'.map f).exists_le_sylow
  have hinter := index_two_sylow_intersection f hcard S hf hS P hSP
  let eP := Identification.sylowEquiv P
  let j : S →* P := (f.comp (S : Subgroup W).subtype).codRestrict P
    (fun u => hSP (mem_map_of_mem f u.property))
  let t : S →* Holomorph.Model := eP.symm.toMonoidHom.comp j
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have ht : Function.Injective t := eP.symm.injective.comp hj
  have href : Holomorph.reflection ∈ t.range := by
    have hm : eP Holomorph.reflection ∈ sylowInner P := by
      rw [← Identification.sylowEquiv_innerD]
      exact mem_map_of_mem _ (subset_closure (by simp))
    have hX : (eP Holomorph.reflection : AutA6) ∈ (S : Subgroup W).map f := by
      change eP Holomorph.reflection ∈ ((S : Subgroup W).map f).subgroupOf P
      rw [hinter]
      exact hinner hm
    obtain ⟨x, hx, he⟩ := hX
    refine ⟨⟨x, hx⟩, ?_⟩
    apply eP.injective
    change eP (eP.symm (j ⟨x, hx⟩)) = eP Holomorph.reflection
    rw [eP.apply_symm_apply]
    exact Subtype.ext he
  let a : S := s.symm (Semidihedral.standardRotation 4 (by decide))
  let b : S := s.symm (Semidihedral.standardReflection 4 (by decide))
  have ha : orderOf a = 8 := by
    rw [s.symm.orderOf_eq]
    exact Semidihedral.standardRotation_order 4 (by decide)
  have hb : b ^ 2 = 1 := by
    have hbo : orderOf b = 2 := (s.symm.orderOf_eq _).trans
      (Semidihedral.standardReflection_order 4 (by decide))
    simpa only [hbo] using pow_orderOf_eq_one b
  have hab : b * a * b⁻¹ = a ^ 3 := by
    simpa only [a, b, map_mul, map_inv, map_pow,
      show 2 ^ (4 - 2) - 1 = 3 from rfl] using
      congrArg s.symm (Semidihedral.standard_conjugation 4 (by decide))
  have hg : closure ({a, b} : Set S) = ⊤ := by
    have he := congrArg (fun K => K.map s.symm.toMonoidHom)
      (Semidihedral.standard_generators 4 (by decide))
    simpa only [a, b, MulEquiv.coe_toMonoidHom, MonoidHom.map_closure,
      Set.image_insert_eq, Set.image_singleton,
      map_top_of_surjective s.symm.toMonoidHom s.symm.surjective] using he
  have hs := range_le_selected t ht a b ha hb hab hg href
  rintro _ ⟨x, hx, rfl⟩
  have hm := selected_mem_extension P (t ⟨x, hx⟩) (hs ⟨⟨x, hx⟩, rfl⟩)
  change (eP (eP.symm (j ⟨x, hx⟩)) : AutA6) ∈ extension at hm
  rwa [eP.apply_symm_apply] at hm

/-- The conjugation image is exactly the specified M₁₀ inside Aut(A₆). -/
theorem conjugation_range_eq_extension {W : Type*} [Group W] [Finite W]
    (N : Subgroup W) [N.Normal] (hi : N.index = 2) (eN : N ≃* A6)
    (S : Sylow 2 W) (s : S ≃* Semidihedral.StandardModel 4 (by decide)) :
    (conjugationAction N eN).range = extension := by
  let f := conjugationAction N eN
  have hf : Function.Injective f := conjugation_injective N hi eN S s
  have hN : Nat.card N = 360 := (Nat.card_congr eN.toEquiv).trans card_A6
  have hW : Nat.card W = 720 := by
    have hc := N.card_mul_index
    rw [hN, hi] at hc
    exact hc.symm
  have hcard : Nat.card f.range = 720 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hW
  have hinner : ShadowLocal.inner ≤ f.range := by
    rw [← conjugationAction_map_inner N eN]
    exact map_le_range f N
  have hS := sylow_image_le_extension f hf hinner hcard S s
  have hNS : N ⊔ (S : Subgroup W) = ⊤ := by
    have hn : ¬ (S : Subgroup W) ≤ N := by
      intro hle
      have hd := index_dvd_of_le hle
      rw [hi] at hd
      exact S.not_dvd_index hd
    obtain ⟨u, huS, huN⟩ : ∃ u, u ∈ (S : Subgroup W) ∧ u ∉ N := by
      by_contra hnex
      apply hn
      intro u hu
      by_contra hun
      exact hnex ⟨u, hu, hun⟩
    apply top_unique
    intro x _
    by_cases hx : x ∈ N
    · exact mem_sup_left hx
    · have hxu : x * u⁻¹ ∈ N :=
        (N.mul_mem_iff_of_index_two hi).mpr (iff_of_false hx (by simpa using huN))
      have he := (N ⊔ (S : Subgroup W)).mul_mem (mem_sup_left hxu) (mem_sup_right huS)
      simpa only [inv_mul_cancel_right] using he
  apply eq_of_le_of_card_ge
  · change f.range ≤ extension
    rw [MonoidHom.range_eq_map, ← hNS, Subgroup.map_sup]
    apply sup_le _ hS
    rw [conjugationAction_map_inner]
    exact Action.inner_le_extension
  · rw [hcard, Action.card_extension]

/-- The actual equivalence marks the original A₆ as the inner subgroup of M₁₀. -/
theorem exists_marked_equiv {W : Type*} [Group W] [Finite W]
    (N : Subgroup W) [N.Normal] (hi : N.index = 2) (eN : N ≃* A6)
    (S : Sylow 2 W) (s : S ≃* Semidihedral.StandardModel 4 (by decide)) :
    ∃ e : W ≃* extension,
      N.map e.toMonoidHom = ShadowLocal.inner.subgroupOf extension := by
  let f := conjugationAction N eN
  let e : W ≃* extension := (MonoidHom.ofInjective (conjugation_injective N hi eN S s)).trans
    (MulEquiv.subgroupCongr (conjugation_range_eq_extension N hi eN S s))
  refine ⟨e, ?_⟩
  apply map_injective extension.subtype_injective
  rw [map_subgroupOf_eq_of_le Action.inner_le_extension, map_map]
  have he : extension.subtype.comp e.toMonoidHom = f := rfl
  rw [he]
  exact conjugationAction_map_inner N eN

end AlternatingSix.M10.SylowRecognition
