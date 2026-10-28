module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SmallModels
public import Theory.PPrimeCore

/-!
# Excluding odd special-linear rows for binary PSL₂

Binary PSL₂ has trivial center, whereas odd SL₂ has a central involution.
An odd kernel on the original binary simple subgroup is trivial, so the
same obstruction survives the containing group's odd-core quotient.
The generation identity in A.3.12(21) makes this image the full quotient.
Source: Aschbacher–Smith A.3.12(9,21,22), pp.47–48, used in C.5.13.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels
universe u
variable {B : Type u} [Group B] {n : ℕ}

theorem binary_not_odd_special_linear (hB : ClassicalGroup.IsPSL B 2 (2^n))
    {p : ℕ} (hp : Odd p) : ¬ IsSL B 2 p := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  have hc := Nat.card_congr (centerCongr e).toEquiv
  rw [binary_center_eq_bot hB,card_bot,Atlas.ExceptionalSupport.card_sl_center,hF] at hc
  have hodd : 2 ∣ p-1 := by
    have hp1 : 1 ≤ p := hp.pos
    obtain ⟨k,hk⟩ := hp
    exact ⟨k,by omega⟩
  have hg : Nat.gcd 2 (p-1) = 2 := Nat.gcd_eq_left_iff_dvd.mpr hodd
  norm_num only [Fintype.card_fin,hg] at hc

theorem binary_odd_kernel_injective [Finite B] (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) {C : Type*} [Group C]
    (f : B →* C) (hk : Nat.Coprime 2 (Nat.card f.ker)) : Function.Injective f := by
  let : IsSimpleGroup B := binary_simple hn hB
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance with he | he
  · exact he
  · have hd : 2 ∣ Nat.card B := by
      rw [binary_card hB]
      apply dvd_mul_of_dvd_left
      exact dvd_pow_self 2 (by omega)
    rw [he,card_top] at hk
    exact (Nat.Prime.not_dvd_one Nat.prime_two
      (Nat.dvd_gcd (dvd_refl 2) hd |>.trans (by rw [hk.gcd_eq_one]))).elim

/-- Factoring an odd core in a containing subgroup preserves the original
binary simple smaller subgroup. -/
theorem binary_odd_core_image_equiv {G : Type*} [Group G] [Finite G]
    (B L : Subgroup G) (hBL : B ≤ L) (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) :
    Nonempty (B ≃* (B.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 L))) := by
  let q := QuotientGroup.mk' (pPrimeCore 2 L)
  let i := inclusion hBL
  let f := q.comp i
  have hk : Nat.Coprime 2 (Nat.card f.ker) := by
    have he : f.ker = (pPrimeCore 2 L).comap i := by
      ext b
      change q (i b) = 1 ↔ i b ∈ pPrimeCore 2 L
      exact QuotientGroup.eq_one_iff (i b)
    rw [he]
    exact pPrimeCore_coprime_card.of_dvd_right
      ((pPrimeCore 2 L).card_comap_dvd_of_injective i (inclusion_injective hBL))
  have hf := binary_odd_kernel_injective hn hB f hk
  have hr : f.range = (B.subgroupOf L).map q := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact mem_map_of_mem q b.property
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b,hb⟩,rfl⟩
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)⟩

/-- The SL₂(5) image required by A.3.12(22) is impossible for the original
binary simple smaller subgroup. -/
theorem binary_not_odd_core_SL_image {G : Type*} [Group G] [Finite G]
    (B L : Subgroup G) (hBL : B ≤ L) (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) {p : ℕ} (hp : Odd p) :
    ¬ IsSL ((B.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 L))) 2 p := by
  intro h
  obtain ⟨e⟩ := binary_odd_core_image_equiv B L hBL hn hB
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
  exact binary_not_odd_special_linear hB hp ⟨F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩
/-- The odd-core supplement alternative A.3.12(21) is likewise impossible;
its generation identity forces the forbidden SL₂ model on the smaller image. -/
theorem binary_not_odd_core_SL_supplement {G : Type*} [Group G] [Finite G]
    (B L : Subgroup G) (hBL : B ≤ L) (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hgen : B ⊔ (pPrimeCore 2 L).map L.subtype = L) {p : ℕ} (hp : Odd p) :
    ¬ IsSL (L ⧸ pPrimeCore 2 L) 2 p := by
  intro h
  let q := QuotientGroup.mk' (pPrimeCore 2 L)
  have hi : B.subgroupOf L ⊔ pPrimeCore 2 L = ⊤ := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBL,← MonoidHom.range_eq_map,range_subtype]
    exact hgen
  have him : (B.subgroupOf L).map q = ⊤ := by
    have hh := congrArg (Subgroup.map q) hi
    simpa only [q,Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using hh
  apply binary_not_odd_core_SL_image B L hBL hn hB hp
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨((MulEquiv.subgroupCongr him).trans topEquiv).trans e⟩⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
