module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalClassification
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalNormalizer
public import Theory.GroupTheory.SylowThreeCubic

/-!
# Cubic normalizers and normal Sylow three-subgroups

Let a subgroup of the first local group have symmetric-three quotient and
an actual Sylow two-subgroup normalized by the opposite local group.
An opposite cubic element acts on that Sylow subgroup. Any invariant normal
subgroup is killed by the faithful overlap normalizer argument, so the
proved local theorem (2.15) makes every Sylow three-subgroup normal.

The conjugation map retains the literal Sylow and ambient embeddings.
This shared step is used in Goldschmidt (4.2), (4.4), and (5.3),
*Automorphisms of trivalent graphs* (1980), pp.392--395.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.normal_three_of_opposite_normalized_sylow
    (h : CubicTreeAction F) (H : Subgroup G) (hHA : H ≤ F false)
    (P : Sylow 2 H)
    (hPT : (P : Subgroup H).map H.subtype ≤ F false ⊓ F true)
    (hBN : F true ≤ normalizer ((P : Subgroup H).map H.subtype : Set G))
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    ∀ S : Sylow 3 H, S.Normal := by
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  let : Finite H := Finite.of_injective (inclusion hHA) (inclusion_injective hHA)
  have hdH : 3 ∣ Nat.card H := by
    rw [SymmetricThreeTwoCore.card_eq e]
    exact dvd_mul_of_dvd_left (by decide) _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 hdH
  obtain ⟨PB, hPB⟩ := h.primitive.sylow.right_sylow
  have hdB : 3 ∣ Nat.card (F true) := by
    have hi : (PB : Subgroup (F true)).index = 3 := by
      rw [hPB]
      exact h.primitive.right_index
    rw [← (PB : Subgroup (F true)).index_mul_card, hi]
    exact dvd_mul_right _ _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := F true) 3 hdB
  let R := (P : Subgroup H).map H.subtype
  let f : P ≃* R := equivMapOfInjective (P : Subgroup H) H.subtype H.subtype_injective
  let yn : normalizer (R : Set G) := ⟨y, hBN y.property⟩
  let a : MulAut P := MulAut.congr f.symm (R.normalizerMonoidHom yn)
  have ha : a ^ 3 = 1 := by
    have hyn : yn ^ 3 = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : F true => (z : G)) (show y ^ 3 = 1 from by rw [← hy]; exact pow_orderOf_eq_one y)
    change (MulAut.congr f.symm (R.normalizerMonoidHom yn)) ^ 3 = 1
    rw [← map_pow, ← map_pow, hyn, map_one, map_one]
  have hact (p : P) : (((a p : P) : H) : G) = (y : G) * (p : G) * (y : G)⁻¹ := by
    change (f (f.symm (R.normalizerMonoidHom yn (f p))) : G) = _
    rw [f.apply_symm_apply]
    rfl
  apply goldschmidt_2_15_normal_sylow_three e P a ha
  intro K hKa hKN
  let D := K.map (P : Subgroup H).subtype
  let L := D.map H.subtype
  have hLP : L ≤ R := map_mono (map_subtype_le K)
  have hLH : L ≤ H := map_subtype_le D
  have hHN : H ≤ normalizer (L : Set G) := by
    let : D.Normal := hKN
    have hh := D.le_normalizer_map H.subtype
    simpa only [D.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hcomp : (MulAut.conj (y : G)).toMonoidHom.comp
      (H.subtype.comp (P : Subgroup H).subtype) =
      (H.subtype.comp (P : Subgroup H).subtype).comp a.toMonoidHom := by
    ext p
    exact (hact p).symm
  have hyN : (y : G) ∈ normalizer (L : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change ((K.map (P : Subgroup H).subtype).map H.subtype).map
      (MulAut.conj (y : G)).toMonoidHom = L
    rw [map_map, map_map, MonoidHom.comp_assoc, hcomp, ← map_map, hKa]
    exact (map_map _ _ _).symm
  let X := (zpowers x).map (inclusion hHA)
  let Y := zpowers y
  have hX : Nat.card X = 3 := by
    rw [card_map_of_injective (inclusion_injective hHA), Nat.card_zpowers, hx]
  have hY : Nat.card Y = 3 := by rw [Nat.card_zpowers, hy]
  have hXN : X.map (F false).subtype ≤ normalizer (L : Set G) := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hHN z.property
  have hYN : Y.map (F true).subtype ≤ normalizer (L : Set G) := by
    rw [map_le_iff_le_comap]
    exact zpowers_le.mpr hyN
  have hL := h.normalized_overlap_eq_bot_of_three_subgroups L (hLP.trans hPT)
    X Y hX hY hXN hYN
  apply (map_eq_bot_iff_of_injective K (P : Subgroup H).subtype_injective).mp
  exact (map_eq_bot_iff_of_injective D H.subtype_injective).mp hL

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
