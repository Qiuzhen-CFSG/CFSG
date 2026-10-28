module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.QuotientAction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.SourceFactors
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Actual factor and actor witnesses for the contrary Sylow group

The full symmetric-three product quotient of `XS` supplies independent
inversion: composing with both sign maps kills `X`, so their joint image is
already supplied by `S`. The actor with signs `(-1,1)` inverts the first
order-three factor and fixes the second. The quotient map restricts to an
embedding of the literal `X/O₂(X)` because `X` is normal in `XS`.

A failure to normalize one of the two actual factors, together with their
permutation by conjugation, supplies an actor interchanging both quotient
images. No coordinates or order-two hypothesis are imposed on that actor.
The quotient witness records both full surjectivity and the actual factor
images; separate surjectivity of the two coordinate projections is insufficient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.4.12(6)
and the embedding step of 15.4.20, printed pp.1160 and 1164.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup

private theorem even_three_commute : ∀ x y : Equiv.Perm (Fin 3),
    Equiv.Perm.sign x = 1 → Equiv.Perm.sign y = 1 → x * y * x⁻¹ = y := by decide

private theorem odd_three_invert : ∀ x y : Equiv.Perm (Fin 3),
    Equiv.Perm.sign x = -1 → Equiv.Perm.sign y = 1 → x * y * x⁻¹ = y⁻¹ := by decide

private theorem independent_sign_actor {H : Type*} [Group H]
    (X S : Subgroup H) (hgen : X ⊔ S = ⊤)
    (f : H →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) (hf : Function.Surjective f)
    (hX : ∀ x ∈ X, Equiv.Perm.sign (f x).1 = 1 ∧ Equiv.Perm.sign (f x).2 = 1) :
    ∃ s : S, Equiv.Perm.sign (f s).1 = -1 ∧ Equiv.Perm.sign (f s).2 = 1 := by
  let r : H →* (ℤˣ × ℤˣ) := (Equiv.Perm.sign.prodMap Equiv.Perm.sign).comp f
  have hXr : X.map r = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact Prod.ext (hX x hx).1 (hX x hx).2
  obtain ⟨y, hy⟩ := hf (Equiv.swap 0 1, 1)
  have hry : r y = (-1,1) := by
    change (Equiv.Perm.sign (f y).1, Equiv.Perm.sign (f y).2) = _
    rw [hy]
    simp [Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)]
  have hmem : r y ∈ S.map r := by
    have hh : r y ∈ (X ⊔ S).map r := ⟨y, hgen ▸ mem_top y, rfl⟩
    simpa only [Subgroup.map_sup, hXr, bot_sup_eq] using hh
  obtain ⟨s, hs, he⟩ := hmem
  have heq : r s = (-1,1) := he.trans hry
  exact ⟨⟨s, hs⟩, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

private theorem exists_core_quotient_embedding {G B : Type*} [Group G] [Group B]
    (X H : Subgroup G) (hXH : X ≤ H) (hn : H ≤ normalizer (X : Set G))
    (f : H →* B) (hker : f.ker = pCore 2 H) :
    ∃ q : (X ⧸ pCore 2 X) →* B, Function.Injective q ∧
      ∀ x : X, q (QuotientGroup.mk' (pCore 2 X) x) = f (inclusion hXH x) := by
  let g := f.comp (inclusion hXH)
  have hg : g.ker = pCore 2 X := by
    apply le_antisymm
    · have he : g.ker = (pCore 2 H).comap (inclusion hXH) := by
        change f.ker.comap (inclusion hXH) = _
        rw [hker]
      rw [he]
      exact le_sSup ⟨inferInstance,
        pCore_isPGroup.comap_of_injective (inclusion hXH) (inclusion_injective hXH)⟩
    · have hc := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X)
        ((pCoreIn_le 2 X).trans hXH)
        (hn.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
      intro x hx
      have hv := hc (show (x : G) ∈ X.pCoreIn 2 from ⟨x,hx,rfl⟩)
      obtain ⟨y, hy, he⟩ := hv
      have hyx : y = inclusion hXH x := Subtype.ext he
      rw [hyx] at hy
      change f (inclusion hXH x) = 1
      exact MonoidHom.mem_ker.mp (hker ▸ hy)
  let q := QuotientGroup.lift (pCore 2 X) g (le_of_eq hg.symm)
  refine ⟨q, ?_, fun x => rfl⟩
  apply (MonoidHom.ker_eq_bot_iff q).mp
  rw [QuotientGroup.ker_lift, hg]
  exact QuotientGroup.map_mk'_self _


/-- Conjugation of ambient factors descends to their actual two-core quotient images. -/
theorem map_quotient_factor {G : Type*} [Group G]
    (X L L' : Subgroup G) (hLX : L ≤ X) (hL'X : L' ≤ X)
    (u : normalizer (X : Set G))
    (he : L.map (MulAut.conj (u : G)).toMonoidHom = L') :
    ((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      (quotientAut (pCore 2 X) (X.normalizerMonoidHom u)).toMonoidHom =
        (L'.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let a := X.normalizerMonoidHom u
  have hc : (quotientAut (pCore 2 X) a).toMonoidHom.comp q = q.comp a.toMonoidHom := by
    ext x
    exact quotientAut_apply_mk (pCore 2 X) a x
  change ((L.subgroupOf X).map q).map (quotientAut (pCore 2 X) a).toMonoidHom = _
  rw [map_map, hc, ← map_map]
  congr 1
  apply Subgroup.map_injective X.subtype_injective
  rw [map_map]
  have heq : X.subtype.comp a.toMonoidHom = (MulAut.conj (u : G)).toMonoidHom.comp X.subtype := rfl
  rw [heq, ← map_map, map_subgroupOf_eq_of_le hLX, he, map_subgroupOf_eq_of_le hL'X]

/-- A moved factor supplies a simultaneous interchange of both quotient images. -/
theorem quotient_factor_exchange_of_movement {G : Type*} [Group G]
    (X U : Subgroup G) (hn : U ≤ normalizer (X : Set G))
    (L : Bool → Subgroup G) (hL : L false ⊔ L true = X)
    (hp : ∀ u ∈ U, ∀ V ∈ ({L false, L true} : Set (Subgroup G)),
      V.map (MulAut.conj u).toMonoidHom ∈ ({L false, L true} : Set (Subgroup G)))
    (i : Bool) (hmove : ¬ U ≤ normalizer (L i : Set G)) :
    ∃ b : U,
      (((L false).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        (quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn b))).toMonoidHom =
          ((L true).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) ∧
      (((L true).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        (quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn b))).toMonoidHom =
          ((L false).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) := by
  have hs : ∃ b ∈ U, (L false).map (MulAut.conj b).toMonoidHom = L true ∧
      (L true).map (MulAut.conj b).toMonoidHom = L false := by
    cases i with
    | false => exact TwoFactors.SourceFactors.swap_of_pair_invariant hp hmove
    | true =>
      have hp' : ∀ u ∈ U, ∀ V ∈ ({L true, L false} : Set (Subgroup G)),
          V.map (MulAut.conj u).toMonoidHom ∈ ({L true, L false} : Set (Subgroup G)) := by
        simpa only [Set.pair_comm (L true) (L false)] using hp
      obtain ⟨b,hb,hb1,hb2⟩ := TwoFactors.SourceFactors.swap_of_pair_invariant hp' hmove
      exact ⟨b,hb,hb2,hb1⟩
  obtain ⟨b,hb,hb1,hb2⟩ := hs
  exact ⟨⟨b,hb⟩,
    map_quotient_factor X _ _ (hL ▸ le_sup_left) (hL ▸ le_sup_right) ⟨b,hn hb⟩ hb1,
    map_quotient_factor X _ _ (hL ▸ le_sup_right) (hL ▸ le_sup_left) ⟨b,hn hb⟩ hb2⟩


private theorem map_factor_through_quotient_embedding {G B : Type*} [Group G] [Group B]
    (X H L : Subgroup G) (hXH : X ≤ H) (hLX : L ≤ X)
    (f : H →* B) (q : (X ⧸ pCore 2 X) →* B)
    (hq : ∀ x : X, q (QuotientGroup.mk' (pCore 2 X) x) = f (inclusion hXH x)) :
    (((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map q) =
      (L.subgroupOf H).map f := by
  have hc : q.comp (QuotientGroup.mk' (pCore 2 X)) = f.comp (inclusion hXH) := by
    ext x
    exact hq x
  rw [map_map, hc, ← map_map]
  congr 1
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hy
    exact ⟨⟨(y : G),hLX hy⟩,hy,rfl⟩

/-- The full `S₃ × S₃` quotient constructs an independent inverter in `S ≤ U`,
and proves generation and order three for the literal factor images in `X/O₂(X)`. -/
theorem independent_inverter_from_product {G : Type*} [Group G] [Finite G]
    (X S U : Subgroup G) (hSU : S ≤ U) (hn : U ≤ normalizer (X : Set G))
    (L : Bool → Subgroup G) (hL : L false ⊔ L true = X)
    (f : (X ⊔ S : Subgroup G) →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hf : Function.Surjective f) (hker : f.ker = pCore 2 (X ⊔ S : Subgroup G))
    (hf1 : ((L false).subgroupOf (X ⊔ S)).map f = (alternatingGroup (Fin 3)).prod ⊥)
    (hf2 : ((L true).subgroupOf (X ⊔ S)).map f = (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3))) :
    let A1 := ((L false).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    let A2 := ((L true).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    A1 ⊔ A2 = ⊤ ∧ Nat.card A1 = 3 ∧ Nat.card A2 = 3 ∧
      ∃ a : U,
        (∀ x ∈ A1, quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn a)) x = x⁻¹) ∧
        (∀ x ∈ A2, quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn a)) x = x) := by
  let H : Subgroup G := X ⊔ S
  have hLX (i : Bool) : L i ≤ X := by
    cases i
    · exact hL ▸ le_sup_left
    · exact hL ▸ le_sup_right
  have hXH : X ≤ H := le_sup_left
  have hSH : S ≤ H := le_sup_right
  have hHX : H ≤ normalizer (X : Set G) := sup_le X.le_normalizer (hSU.trans hn)
  obtain ⟨q,hqi,hq⟩ := exists_core_quotient_embedding X H hXH hHX f hker
  let A1 := ((L false).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  let A2 := ((L true).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  have hA1 : A1.map q = (alternatingGroup (Fin 3)).prod ⊥ :=
    (map_factor_through_quotient_embedding X H _ hXH (hLX false) f q hq).trans hf1
  have hA2 : A2.map q = (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) :=
    (map_factor_through_quotient_embedding X H _ hXH (hLX true) f q hq).trans hf2
  have hgen : A1 ⊔ A2 = ⊤ := by
    rw [← Subgroup.map_sup, ← subgroupOf_sup (hLX false) (hLX true), hL, subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hcard1 : Nat.card A1 = 3 := by
    rw [← card_map_of_injective hqi, hA1]
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
    rw [nat_card_alternatingGroup]
    norm_num
  have hcard2 : Nat.card A2 = 3 := by
    rw [← card_map_of_injective hqi, hA2]
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
    rw [nat_card_alternatingGroup]
    norm_num
  have hgenH : X.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup hXH hSH]
    exact subgroupOf_self H
  have hXmap : (X.subgroupOf H).map f ≤ (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) := by
    have he := congrArg (fun D : Subgroup G => D.subgroupOf H) hL
    rw [subgroupOf_sup ((hLX false).trans hXH) ((hLX true).trans hXH)] at he
    rw [← he, Subgroup.map_sup]
    rw [hf1, hf2]
    exact sup_le (prod_mono le_rfl bot_le) (prod_mono bot_le le_rfl)
  obtain ⟨s,hs1,hs2⟩ := independent_sign_actor (X.subgroupOf H) (S.subgroupOf H) hgenH f hf
    (fun x hx => by
      have hh := hXmap (show f x ∈ (X.subgroupOf H).map f from ⟨x,hx,rfl⟩)
      exact ⟨Equiv.Perm.mem_alternatingGroup.mp hh.1, Equiv.Perm.mem_alternatingGroup.mp hh.2⟩)
  let a : U := ⟨((s : H) : G),hSU s.property⟩
  have hact (x : X ⧸ pCore 2 X) :
      q (quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn a)) x) =
        f (s : H) * q x * (f (s : H))⁻¹ := by
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) x
    rw [quotientAut_apply_mk, hq, hq]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨hgen,hcard1,hcard2,a,?_,?_⟩
  · intro x hx
    apply hqi
    rw [hact, map_inv]
    have hxq := hA1 ▸ (show q x ∈ A1.map q from ⟨x,hx,rfl⟩)
    apply Prod.ext
    · exact odd_three_invert _ _ hs1 (Equiv.Perm.mem_alternatingGroup.mp hxq.1)
    · have hh : (q x).2 = 1 := mem_bot.mp hxq.2
      simp [hh]
  · intro x hx
    apply hqi
    rw [hact]
    have hxq := hA2 ▸ (show q x ∈ A2.map q from ⟨x,hx,rfl⟩)
    apply Prod.ext
    · have hh : (q x).1 = 1 := mem_bot.mp hxq.1
      simp [hh]
    · exact even_three_commute _ _ hs2 (Equiv.Perm.mem_alternatingGroup.mp hxq.2)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
